package p

type Storage struct{}

func (s Storage) GetItem(key string) string { return "" }
func (s Storage) SetItem(key, value string) {}
func (s Storage) RemoveItem(key string)     {}

func useSelector(s Storage) {
	_ = s.Get1Item("x") // want "unknown selector"
}
