package p

var saveRef int

func useIdentifier() {
	_ = saveRe1f // want "undefined identifier"
}
