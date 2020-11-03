package flatbuffers

// FlatBuffer is the interface that represents a flatbuffer.
type FlatBuffer interface {
	Table() Table
	Init(buf []byte, i UOffsetT)
}

// GetRootAs is a generic helper to initialize a FlatBuffer with the provided buffer bytes and its data offset.
func GetRootAs(buf []byte, offset UOffsetT, fb FlatBuffer) {
	n := GetUOffsetT(buf[offset:])
	fb.Init(buf, n+offset)
}

// GetSizePrefix reads the size from a size-prefixed flatbuffer
func GetSizePrefix(buf []byte) uint32 {
	return GetUint32(buf)
}

// RemoveSizePrefix returns a slice of the original buffer starting from right after the prefixed size
func RemoveSizePrefix(buf []byte) []byte {
	return buf[sizePrefixLength:]
}
