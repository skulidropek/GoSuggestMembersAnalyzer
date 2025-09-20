package smbgo

import (
	"fmt"
	"go/ast"
	"go/types"
	"io/fs"
	"os"
	"path"
	"path/filepath"
	"sort"
	"strconv"
	"strings"

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
	identPool   []string
}

type moduleInfo struct {
	modPath  string
	modRoot  string
	packages []string
}

func run(pass *analysis.Pass) (any, error) {
	state := &analyzerState{
		pass:        pass,
		moduleCache: make(map[string]*moduleInfo),
		identPool:   collectIdentifierPool(pass),
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
			members := collectPackageMembers(pkg)
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

	candidates := similarMembers(name, xType)
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

	message := fmt.Sprintf("cannot resolve import %q; did you mean:%s", raw, formatCandidates(candidates))

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

func collectIdentifierPool(pass *analysis.Pass) []string {
	seen := make(map[string]struct{})

	for ident, obj := range pass.TypesInfo.Defs {
		if obj == nil {
			continue
		}
		name := ident.Name
		if name == "" || name == "_" {
			continue
		}
		seen[name] = struct{}{}
	}

	for ident, obj := range pass.TypesInfo.Uses {
		if obj == nil {
			continue
		}
		name := ident.Name
		if name == "" || name == "_" {
			continue
		}
		seen[name] = struct{}{}
	}

	if pass.Pkg != nil {
		for _, name := range pass.Pkg.Scope().Names() {
			if name == "" || name == "_" {
				continue
			}
			seen[name] = struct{}{}
		}
	}

	result := make([]string, 0, len(seen))
	for name := range seen {
		result = append(result, name)
	}
	sort.Strings(result)
	return result
}

func similarMembers(name string, typ types.Type) []string {
	members := collectMembers(typ)
	return topSimilar(name, members, maxSelectorDistance(name), 5)
}

func collectPackageMembers(pkg *types.Package) []string {
	scope := pkg.Scope()
	names := scope.Names()
	out := make([]string, 0, len(names))
	for _, name := range names {
		if ast.IsExported(name) {
			out = append(out, name)
		}
	}
	sort.Strings(out)
	return out
}

func collectMembers(t types.Type) []string {
	names := make(map[string]struct{})

	add := func(name string) {
		if name == "" {
			return
		}
		names[name] = struct{}{}
	}

	base := t
	if ptr, ok := t.(*types.Pointer); ok {
		base = ptr.Elem()
	}

	if st, ok := base.Underlying().(*types.Struct); ok {
		for i := 0; i < st.NumFields(); i++ {
			add(st.Field(i).Name())
		}
	}

	addMethodSet := func(typ types.Type) {
		ms := types.NewMethodSet(typ)
		for i := 0; i < ms.Len(); i++ {
			add(ms.At(i).Obj().Name())
		}
	}

	addMethodSet(t)
	addMethodSet(types.NewPointer(base))

	result := make([]string, 0, len(names))
	for name := range names {
		result = append(result, name)
	}
	sort.Strings(result)
	return result
}

func topSimilar(target string, pool []string, maxDist, limit int) []string {
	if target == "" || limit <= 0 {
		return nil
	}

	type candidate struct {
		value string
		dist  int
		size  int
	}

	targetLower := strings.ToLower(target)
	var candidates []candidate
	seen := make(map[string]struct{})

	for _, option := range pool {
		if option == "" {
			continue
		}
		if _, ok := seen[option]; ok {
			continue
		}
		seen[option] = struct{}{}

		if strings.EqualFold(option, target) {
			continue
		}

		dist := editDistance(targetLower, strings.ToLower(option))
		if dist > maxDist {
			continue
		}
		candidates = append(candidates, candidate{value: option, dist: dist, size: len(option)})
	}

	sort.Slice(candidates, func(i, j int) bool {
		if candidates[i].dist != candidates[j].dist {
			return candidates[i].dist < candidates[j].dist
		}
		if candidates[i].size != candidates[j].size {
			return candidates[i].size < candidates[j].size
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

func formatCandidates(candidates []string) string {
	if len(candidates) == 0 {
		return ""
	}
	var b strings.Builder
	for _, cand := range candidates {
		b.WriteString("\n  - ")
		b.WriteString(cand)
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
