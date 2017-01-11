// automatically generated by the FlatBuffers compiler, do not modify

package KeySearch

import (
	flatbuffers "github.com/google/flatbuffers/go"
)

type BoolEntry struct {
	_tab flatbuffers.Table
}

func GetRootAsBoolEntry(buf []byte, offset flatbuffers.UOffsetT) *BoolEntry {
	n := flatbuffers.GetUOffsetT(buf[offset:])
	x := &BoolEntry{}
	x.Init(buf, n+offset)
	return x
}

func (rcv *BoolEntry) Init(buf []byte, i flatbuffers.UOffsetT) {
	rcv._tab.Bytes = buf
	rcv._tab.Pos = i
}

func (rcv *BoolEntry) Table() flatbuffers.Table {
	return rcv._tab
}

func (rcv *BoolEntry) Key() byte {
	o := flatbuffers.UOffsetT(rcv._tab.Offset(4))
	if o != 0 {
		return rcv._tab.GetByte(o + rcv._tab.Pos)
	}
	return 0
}

func (rcv *BoolEntry) MutateKey(n byte) bool {
	return rcv._tab.MutateByteSlot(4, n)
}

func (rcv *BoolEntry) Value() byte {
	o := flatbuffers.UOffsetT(rcv._tab.Offset(6))
	if o != 0 {
		return rcv._tab.GetByte(o + rcv._tab.Pos)
	}
	return 1
}

func (rcv *BoolEntry) MutateValue(n byte) bool {
	return rcv._tab.MutateByteSlot(6, n)
}

func BoolEntryStart(builder *flatbuffers.Builder) {
	builder.StartObject(2)
}
func BoolEntryAddKey(builder *flatbuffers.Builder, key byte) {
	builder.PrependByteSlot(0, key, 0)
}
func BoolEntryAddValue(builder *flatbuffers.Builder, value byte) {
	builder.PrependByteSlot(1, value, 1)
}
func BoolEntryEnd(builder *flatbuffers.Builder) flatbuffers.UOffsetT {
	return builder.EndObject()
}
