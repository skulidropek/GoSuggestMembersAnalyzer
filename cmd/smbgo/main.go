package main

import (
	"github.com/you/smbgo/smbgo"
	"golang.org/x/tools/go/analysis/singlechecker"
)

func main() {
	singlechecker.Main(smbgo.Analyzer)
}
