package p

import "fmt"

func usePackageSelector() {
	fmt.Sprin1tf("hello %s", "world") // want "unknown selector \"Sprin1tf\" in package fmt"
}
