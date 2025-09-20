package p

func useBuiltin() []int {
	var xs []int
	xs = app1end(xs, 42) // want "undefined identifier \"app1end\"; did you mean:\n  - append"
	return xs
}
