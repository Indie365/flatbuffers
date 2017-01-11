// automatically generated by the FlatBuffers compiler, do not modify

package KeySearch

import (
	flatbuffers "github.com/google/flatbuffers/go"
)

type LongEntry struct {
	_tab flatbuffers.Table
}

func GetRootAsLongEntry(buf []byte, offset flatbuffers.UOffsetT) *LongEntry {
	n := flatbuffers.GetUOffsetT(buf[offset:])
	x := &LongEntry{}
	x.Init(buf, n+offset)
	return x
}

func (rcv *LongEntry) Init(buf []byte, i flatbuffers.UOffsetT) {
	rcv._tab.Bytes = buf
	rcv._tab.Pos = i
}

func (rcv *LongEntry) Table() flatbuffers.Table {
	return rcv._tab
}

func (rcv *LongEntry) Key() int64 {
	o := flatbuffers.UOffsetT(rcv._tab.Offset(4))
	if o != 0 {
		return rcv._tab.GetInt64(o + rcv._tab.Pos)
	}
	return 0
}

func (rcv *LongEntry) MutateKey(n int64) bool {
	return rcv._tab.MutateInt64Slot(4, n)
}

func (rcv *LongEntry) Value() int64 {
	o := flatbuffers.UOffsetT(rcv._tab.Offset(6))
	if o != 0 {
		return rcv._tab.GetInt64(o + rcv._tab.Pos)
	}
	return -9223372036854775808
}

func (rcv *LongEntry) MutateValue(n int64) bool {
	return rcv._tab.MutateInt64Slot(6, n)
}

func LongEntryStart(builder *flatbuffers.Builder) {
	builder.StartObject(2)
}
func LongEntryAddKey(builder *flatbuffers.Builder, key int64) {
	builder.PrependInt64Slot(0, key, 0)
}
func LongEntryAddValue(builder *flatbuffers.Builder, value int64) {
	builder.PrependInt64Slot(1, value, -9223372036854775808)
}
func LongEntryEnd(builder *flatbuffers.Builder) flatbuffers.UOffsetT {
	return builder.EndObject()
}
