package main

import (
	"github.com/skulidropek/GoSuggestMembersAnalyzer/smbgo"
	"golang.org/x/tools/go/analysis/singlechecker"
)

func main() {
	singlechecker.Main(smbgo.Analyzer)
}
