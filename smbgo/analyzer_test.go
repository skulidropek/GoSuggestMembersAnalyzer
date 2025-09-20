package smbgo_test

import (
	"path/filepath"
	"testing"

	"github.com/you/smbgo/smbgo"
	"golang.org/x/tools/go/analysis/analysistest"
)

func TestAnalyzerSuggestions(t *testing.T) {
	testdata := analysistest.TestData()
	analysistest.Run(t, testdata, smbgo.Analyzer, filepath.Join("p"))
}
