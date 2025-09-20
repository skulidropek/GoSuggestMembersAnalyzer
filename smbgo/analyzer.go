package smbgo

import (
	"bytes"
	"fmt"
	"go/ast"
	"go/build"
	"go/format"
	"go/parser"
	"go/token"
	"go/types"
	"io/fs"
	"os"
	"path"
	"path/filepath"
	"sort"
	"strconv"
	"strings"
	"sync"

	"golang.org/x/mod/modfile"
	"golang.org/x/tools/go/analysis"
)

// Analyzer provides typo suggestions for selectors, identifiers, and import paths.
var Analyzer = &analysis.Analyzer{
	Name:             "smbgo",
	Doc:              "Suggests fixes for likely typos in selectors, identifiers, and import paths",
	Run:              run,
	RunDespiteErrors: true,
}

type analyzerState struct {
	pass        *analysis.Pass
	moduleCache map[string]*moduleInfo
	identPool   []suggestion
}

type moduleInfo struct {
	modPath  string
	modRoot  string
	packages []string
}

type suggestion struct {
	Name  string
	Label string
}

var (
	builtinSigOnce    sync.Once
	builtinSignatures map[string]string
)

func run(pass *analysis.Pass) (any, error) {
	state := &analyzerState{
		pass:        pass,
		moduleCache: make(map[string]*moduleInfo),
		identPool:   collectIdentifierSuggestions(pass),
	}

	for _, file := range pass.Files {
		state.inspectFile(file)
	}

	return nil, nil
}

func (s *analyzerState) inspectFile(file *ast.File) {
	var parents []ast.Node
	filename := s.pass.Fset.File(file.Pos()).Name()

	ast.Inspect(file, func(n ast.Node) bool {
		if n == nil {
			if len(parents) > 0 {
				parents = parents[:len(parents)-1]
			}
			return false
		}

		var parent ast.Node
		if len(parents) > 0 {
			parent = parents[len(parents)-1]
		}

		switch node := n.(type) {
		case *ast.SelectorExpr:
			s.handleSelector(node)
		case *ast.Ident:
			s.handleIdent(node, parent)
		case *ast.ImportSpec:
			s.handleImport(node, filename)
		}

		parents = append(parents, n)
		return true
	})
}

func (s *analyzerState) handleSelector(sel *ast.SelectorExpr) {
	if s.pass.TypesInfo.Selections[sel] != nil {
		return
	}
	if s.pass.TypesInfo.Uses[sel.Sel] != nil {
		return
	}

	name := sel.Sel.Name
	if name == "" {
		return
	}

	if ident, ok := sel.X.(*ast.Ident); ok {
		if pkgName, ok := s.pass.TypesInfo.Uses[ident].(*types.PkgName); ok && pkgName != nil {
			pkg := pkgName.Imported()
			if pkg == nil {
				return
			}
			members := collectPackageMembers(pkg, types.RelativeTo(s.pass.Pkg))
			candidates := topSimilar(name, members, maxSelectorDistance(name), 5)
			if len(candidates) == 0 {
				return
			}
			message := fmt.Sprintf("unknown selector %q in package %s; did you mean:%s", name, pkg.Path(), formatCandidates(candidates))
			s.pass.Report(analysis.Diagnostic{
				Pos:     sel.Sel.Pos(),
				End:     sel.Sel.End(),
				Message: message,
			})
			return
		}
	}

	xType := s.pass.TypesInfo.TypeOf(sel.X)
	if xType == nil {
		return
	}

	candidates := similarMembers(name, xType, s.pass.Pkg)
	if len(candidates) == 0 {
		return
	}

	typeName := types.TypeString(xType, types.RelativeTo(s.pass.Pkg))
	message := fmt.Sprintf("unknown selector %q on %s; did you mean:%s", name, typeName, formatCandidates(candidates))

	s.pass.Report(analysis.Diagnostic{
		Pos:     sel.Sel.Pos(),
		End:     sel.Sel.End(),
		Message: message,
	})
}

func (s *analyzerState) handleIdent(id *ast.Ident, parent ast.Node) {
	if id.Name == "" || id.Name == "_" {
		return
	}

	if _, ok := parent.(*ast.File); ok {
		return
	}

	if s.pass.TypesInfo.Defs[id] != nil || s.pass.TypesInfo.Uses[id] != nil {
		return
	}

	switch p := parent.(type) {
	case *ast.SelectorExpr:
		if p.Sel == id {
			return
		}
	case *ast.Field:
		if p.Names != nil {
			for _, name := range p.Names {
				if name == id {
					return
				}
			}
		}
	case *ast.ImportSpec:
		if p.Name == id {
			return
		}
	}

	candidates := topSimilar(id.Name, s.identPool, maxIdentifierDistance(id.Name), 5)
	if len(candidates) == 0 {
		return
	}

	message := fmt.Sprintf("undefined identifier %q; did you mean:%s", id.Name, formatCandidates(candidates))

	s.pass.Report(analysis.Diagnostic{
		Pos:     id.Pos(),
		End:     id.End(),
		Message: message,
	})
}

func (s *analyzerState) handleImport(spec *ast.ImportSpec, filename string) {
	if spec.Path == nil {
		return
	}

	raw, err := strconv.Unquote(spec.Path.Value)
	if err != nil {
		raw = strings.Trim(spec.Path.Value, "\"")
	}
	if raw == "" {
		return
	}

	info := s.moduleInfoForFile(filename)
	if info == nil || len(info.packages) == 0 {
		return
	}

	if !strings.HasPrefix(raw, info.modPath) {
		if pkgName := s.pass.TypesInfo.PkgNameOf(spec); pkgName != nil && pkgName.Imported() != nil {
			return
		}
		return
	}

	if containsString(info.packages, raw) {
		return
	}

	candidates := similarImportPaths(raw, info.packages, 5)
	if len(candidates) == 0 {
		return
	}

	importSuggestions := make([]suggestion, len(candidates))
	for i, cand := range candidates {
		importSuggestions[i] = suggestion{Name: cand, Label: cand}
	}

	message := fmt.Sprintf("cannot resolve import %q; did you mean:%s", raw, formatCandidates(importSuggestions))

	s.pass.Report(analysis.Diagnostic{
		Pos:     spec.Path.Pos(),
		End:     spec.Path.End(),
		Message: message,
	})
}

func (s *analyzerState) moduleInfoForFile(filename string) *moduleInfo {
	modPath, modRoot := findModuleForFile(filename)
	if modRoot == "" {
		return nil
	}

	if info, ok := s.moduleCache[modRoot]; ok {
		return info
	}

	info := &moduleInfo{modPath: modPath, modRoot: modRoot}
	info.packages = collectModulePackages(modRoot, modPath)
	s.moduleCache[modRoot] = info
	return info
}

func collectIdentifierSuggestions(pass *analysis.Pass) []suggestion {
	qualifier := types.RelativeTo(pass.Pkg)
	seen := make(map[string]string)

	add := func(name, label string) {
		if name == "" || name == "_" {
			return
		}
		if label == "" {
			label = name
		}
		if existing, ok := seen[name]; !ok || len(label) > len(existing) {
			seen[name] = label
		}
	}

	for ident, obj := range pass.TypesInfo.Defs {
		if obj == nil {
			continue
		}
		add(ident.Name, describeObject(obj, qualifier))
	}

	for ident, obj := range pass.TypesInfo.Uses {
		if obj == nil {
			continue
		}
		add(ident.Name, describeObject(obj, qualifier))
	}

	if pass.Pkg != nil {
		scope := pass.Pkg.Scope()
		for _, name := range scope.Names() {
			add(name, describeObject(scope.Lookup(name), qualifier))
		}
	}

	universe := types.Universe
	for _, name := range universe.Names() {
		add(name, describeObject(universe.Lookup(name), qualifier))
	}

	result := make([]suggestion, 0, len(seen))
	for name, label := range seen {
		result = append(result, suggestion{Name: name, Label: label})
	}
	sort.Slice(result, func(i, j int) bool {
		return result[i].Name < result[j].Name
	})
	return result
}

func builtinLabel(name string) string {
	builtinSigOnce.Do(loadBuiltinSignatures)
	if builtinSignatures == nil {
		return ""
	}
	return builtinSignatures[name]
}

func loadBuiltinSignatures() {
	info, err := build.Default.Import("builtin", "", build.FindOnly)
	if err != nil {
		return
	}
	entries := make(map[string]string)
	fset := token.NewFileSet()

	files, err := os.ReadDir(info.Dir)
	if err != nil {
		return
	}

	for _, entry := range files {
		if entry.IsDir() || !strings.HasSuffix(entry.Name(), ".go") {
			continue
		}

		path := filepath.Join(info.Dir, entry.Name())
		file, err := parser.ParseFile(fset, path, nil, parser.SkipObjectResolution)
		if err != nil {
			continue
		}

		for _, decl := range file.Decls {
			fn, ok := decl.(*ast.FuncDecl)
			if !ok || fn.Name == nil {
				continue
			}
			var buf bytes.Buffer
			if err := format.Node(&buf, fset, fn.Type); err != nil {
				continue
			}
			sig := strings.TrimPrefix(buf.String(), "func")
			label := fn.Name.Name + sig
			entries[fn.Name.Name] = strings.TrimSpace(label)
		}
	}

	builtinSignatures = entries
}

func describeObject(obj types.Object, qualifier types.Qualifier) string {
	if obj == nil {
		return ""
	}

	name := obj.Name()
	if name == "" {
		return ""
	}

	typ := obj.Type()
	switch specific := obj.(type) {
	case *types.Func:
		if sig, ok := typ.(*types.Signature); ok {
			return formatFunctionLabel(name, sig, qualifier)
		}
	case *types.Var:
		typeStr := ""
		if typ != nil {
			typeStr = types.TypeString(typ, qualifier)
		}
		if typeStr != "" {
			return fmt.Sprintf("%s %s", name, typeStr)
		}
	case *types.Const:
		if typ != nil {
			return fmt.Sprintf("%s %s", name, types.TypeString(typ, qualifier))
		}
	case *types.TypeName:
		if typ != nil {
			underlying := typ
			if named, ok := typ.(*types.Named); ok {
				underlying = named.Underlying()
			}
			if specific.IsAlias() {
				return fmt.Sprintf("%s = %s", name, types.TypeString(underlying, qualifier))
			}
			return fmt.Sprintf("%s %s", name, types.TypeString(underlying, qualifier))
		}
	case *types.Builtin:
		if label := builtinLabel(name); label != "" {
			return label
		}
		if sig, ok := typ.(*types.Signature); ok {
			return formatFunctionLabel(name, sig, qualifier)
		}
		if typ != nil {
			typeStr := types.TypeString(typ, qualifier)
			if typeStr != "" && typeStr != name {
				return fmt.Sprintf("%s %s", name, typeStr)
			}
		}
	}

	if typ != nil {
		return fmt.Sprintf("%s %s", name, types.TypeString(typ, qualifier))
	}
	return name
}

func formatFunctionLabel(name string, sig *types.Signature, qualifier types.Qualifier) string {
	var b strings.Builder
	if recv := sig.Recv(); recv != nil {
		recvType := types.TypeString(recv.Type(), qualifier)
		b.WriteString("(")
		if recv.Name() != "" {
			b.WriteString(recv.Name())
			b.WriteString(" ")
		}
		b.WriteString(recvType)
		b.WriteString(").")
	}

	b.WriteString(name)
	b.WriteString("(")
	b.WriteString(formatParameters(sig.Params(), sig.Variadic(), qualifier))
	b.WriteString(")")

	if res := formatResults(sig.Results(), qualifier); res != "" {
		b.WriteString(" ")
		b.WriteString(res)
	}

	return b.String()
}

func formatParameters(tuple *types.Tuple, variadic bool, qualifier types.Qualifier) string {
	if tuple == nil || tuple.Len() == 0 {
		return ""
	}
	parts := make([]string, 0, tuple.Len())
	for i := 0; i < tuple.Len(); i++ {
		v := tuple.At(i)
		if v == nil {
			continue
		}
		typ := v.Type()
		typeStr := ""
		if typ != nil {
			typeStr = types.TypeString(typ, qualifier)
		}
		if variadic && i == tuple.Len()-1 {
			if slice, ok := typ.(*types.Slice); ok {
				typeStr = "..." + types.TypeString(slice.Elem(), qualifier)
			}
		}
		if v.Name() != "" {
			parts = append(parts, fmt.Sprintf("%s %s", v.Name(), typeStr))
		} else {
			parts = append(parts, typeStr)
		}
	}
	return strings.Join(parts, ", ")
}

func formatResults(tuple *types.Tuple, qualifier types.Qualifier) string {
	if tuple == nil || tuple.Len() == 0 {
		return ""
	}
	if tuple.Len() == 1 && tuple.At(0).Name() == "" {
		return types.TypeString(tuple.At(0).Type(), qualifier)
	}
	parts := make([]string, 0, tuple.Len())
	for i := 0; i < tuple.Len(); i++ {
		v := tuple.At(i)
		if v == nil {
			continue
		}
		typeStr := types.TypeString(v.Type(), qualifier)
		if v.Name() != "" {
			parts = append(parts, fmt.Sprintf("%s %s", v.Name(), typeStr))
		} else {
			parts = append(parts, typeStr)
		}
	}
	return fmt.Sprintf("(%s)", strings.Join(parts, ", "))
}

func similarMembers(name string, typ types.Type, pkg *types.Package) []suggestion {
	members := collectMembers(typ, types.RelativeTo(pkg))
	return topSimilar(name, members, maxSelectorDistance(name), 5)
}

func collectPackageMembers(pkg *types.Package, qualifier types.Qualifier) []suggestion {
	scope := pkg.Scope()
	names := scope.Names()
	lookup := func(name string) suggestion {
		obj := scope.Lookup(name)
		label := describeObject(obj, qualifier)
		return suggestion{Name: name, Label: label}
	}

	result := make([]suggestion, 0, len(names))
	seen := make(map[string]suggestion)
	for _, name := range names {
		if !ast.IsExported(name) {
			continue
		}
		sugg := lookup(name)
		if existing, ok := seen[sugg.Name]; !ok || len(sugg.Label) > len(existing.Label) {
			seen[sugg.Name] = sugg
		}
	}
	for _, sugg := range seen {
		result = append(result, sugg)
	}
	sort.Slice(result, func(i, j int) bool {
		return result[i].Name < result[j].Name
	})
	return result
}

func collectMembers(t types.Type, qualifier types.Qualifier) []suggestion {
	entries := make(map[string]suggestion)

	add := func(name, label string) {
		if name == "" {
			return
		}
		if label == "" {
			label = name
		}
		if existing, ok := entries[name]; !ok || len(label) > len(existing.Label) {
			entries[name] = suggestion{Name: name, Label: label}
		}
	}

	base := t
	if ptr, ok := t.(*types.Pointer); ok {
		base = ptr.Elem()
	}

	if st, ok := base.Underlying().(*types.Struct); ok {
		for i := 0; i < st.NumFields(); i++ {
			field := st.Field(i)
			name := field.Name()
			if name == "" {
				continue
			}
			label := fmt.Sprintf("%s %s", name, types.TypeString(field.Type(), qualifier))
			add(name, label)
		}
	}

	addMethodSet := func(typ types.Type) {
		ms := types.NewMethodSet(typ)
		for i := 0; i < ms.Len(); i++ {
			obj := ms.At(i).Obj()
			name := obj.Name()
			if name == "" {
				continue
			}
			label := describeObject(obj, qualifier)
			add(name, label)
		}
	}

	addMethodSet(t)
	addMethodSet(types.NewPointer(base))

	result := make([]suggestion, 0, len(entries))
	for _, sugg := range entries {
		result = append(result, sugg)
	}
	sort.Slice(result, func(i, j int) bool {
		return result[i].Name < result[j].Name
	})
	return result
}

func topSimilar(target string, pool []suggestion, maxDist, limit int) []suggestion {
	if target == "" || limit <= 0 {
		return nil
	}

	type candidate struct {
		suggestion suggestion
		dist       int
		size       int
	}

	targetLower := strings.ToLower(target)
	var candidates []candidate
	seen := make(map[string]struct{})

	for _, option := range pool {
		if option.Name == "" {
			continue
		}
		lowerName := strings.ToLower(option.Name)
		if _, ok := seen[lowerName]; ok {
			continue
		}
		seen[lowerName] = struct{}{}

		if lowerName == targetLower {
			continue
		}

		dist := editDistance(targetLower, lowerName)
		if dist > maxDist {
			continue
		}
		candidates = append(candidates, candidate{suggestion: option, dist: dist, size: len(option.Name)})
	}

	sort.Slice(candidates, func(i, j int) bool {
		if candidates[i].dist != candidates[j].dist {
			return candidates[i].dist < candidates[j].dist
		}
		if candidates[i].size != candidates[j].size {
			return candidates[i].size < candidates[j].size
		}
		return candidates[i].suggestion.Name < candidates[j].suggestion.Name
	})

	if len(candidates) > limit {
		candidates = candidates[:limit]
	}

	result := make([]suggestion, len(candidates))
	for i, cand := range candidates {
		result[i] = cand.suggestion
	}
	return result
}

func similarImportPaths(target string, pool []string, limit int) []string {
	if target == "" {
		return nil
	}

	type candidate struct {
		value    string
		baseDist int
		fullDist int
	}

	targetLower := strings.ToLower(target)
	targetBase := strings.ToLower(path.Base(target))

	var candidates []candidate
	seen := make(map[string]struct{})

	for _, option := range pool {
		if option == "" {
			continue
		}
		if strings.EqualFold(option, target) {
			continue
		}
		lower := strings.ToLower(option)
		if _, ok := seen[lower]; ok {
			continue
		}
		seen[lower] = struct{}{}

		base := strings.ToLower(path.Base(option))
		baseDist := editDistance(targetBase, base)
		fullDist := editDistance(targetLower, lower)

		if baseDist > 3 && fullDist > 4 {
			continue
		}

		candidates = append(candidates, candidate{value: option, baseDist: baseDist, fullDist: fullDist})
	}

	sort.Slice(candidates, func(i, j int) bool {
		if candidates[i].baseDist != candidates[j].baseDist {
			return candidates[i].baseDist < candidates[j].baseDist
		}
		if candidates[i].fullDist != candidates[j].fullDist {
			return candidates[i].fullDist < candidates[j].fullDist
		}
		return candidates[i].value < candidates[j].value
	})

	if len(candidates) > limit {
		candidates = candidates[:limit]
	}

	result := make([]string, len(candidates))
	for i, cand := range candidates {
		result[i] = cand.value
	}
	return result
}

func findModuleForFile(filename string) (modPath, modRoot string) {
	dir := filepath.Dir(filename)
	for {
		goMod := filepath.Join(dir, "go.mod")
		data, err := os.ReadFile(goMod)
		if err == nil {
			if mf, err := modfile.Parse("go.mod", data, nil); err == nil && mf.Module != nil {
				return mf.Module.Mod.Path, dir
			}
		}

		parent := filepath.Dir(dir)
		if parent == dir {
			break
		}
		dir = parent
	}
	return "", ""
}

func collectModulePackages(root, modPath string) []string {
	if root == "" || modPath == "" {
		return nil
	}

	seen := make(map[string]struct{})

	filepath.WalkDir(root, func(fullPath string, d fs.DirEntry, err error) error {
		if err != nil {
			return nil
		}
		if d.IsDir() {
			name := d.Name()
			if strings.HasPrefix(name, ".") || name == "vendor" || name == "testdata" {
				return filepath.SkipDir
			}
			return nil
		}
		if !strings.HasSuffix(fullPath, ".go") {
			return nil
		}

		dir := filepath.Dir(fullPath)
		rel, err := filepath.Rel(root, dir)
		if err != nil {
			return nil
		}

		pkg := modPath
		rel = filepath.ToSlash(rel)
		if rel != "." {
			pkg = path.Join(modPath, rel)
		}
		seen[pkg] = struct{}{}
		return nil
	})

	result := make([]string, 0, len(seen))
	for pkg := range seen {
		result = append(result, pkg)
	}
	sort.Strings(result)
	return result
}

func formatCandidates(candidates []suggestion) string {
	if len(candidates) == 0 {
		return ""
	}
	var b strings.Builder
	for _, cand := range candidates {
		b.WriteString("\n  - ")
		label := cand.Label
		if label == "" {
			label = cand.Name
		}
		b.WriteString(label)
	}
	return b.String()
}

func maxIdentifierDistance(name string) int {
	if len(name) <= 3 {
		return 1
	}
	if len(name) <= 6 {
		return 2
	}
	return 3
}

func maxSelectorDistance(name string) int {
	if len(name) <= 4 {
		return 1
	}
	return 2
}

func containsString(list []string, target string) bool {
	for _, s := range list {
		if s == target {
			return true
		}
	}
	return false
}

func editDistance(a, b string) int {
	ra := []rune(a)
	rb := []rune(b)
	m, n := len(ra), len(rb)

	if m == 0 {
		return n
	}
	if n == 0 {
		return m
	}

	prev := make([]int, n+1)
	curr := make([]int, n+1)

	for j := 0; j <= n; j++ {
		prev[j] = j
	}

	for i := 1; i <= m; i++ {
		curr[0] = i
		for j := 1; j <= n; j++ {
			cost := 0
			if ra[i-1] != rb[j-1] {
				cost = 1
			}

			insert := curr[j-1] + 1
			delete := prev[j] + 1
			replace := prev[j-1] + cost

			curr[j] = min3(insert, delete, replace)
		}
		copy(prev, curr)
	}

	return prev[n]
}

func min3(a, b, c int) int {
	if a < b {
		if a < c {
			return a
		}
		return c
	}
	if b < c {
		return b
	}
	return c
}
