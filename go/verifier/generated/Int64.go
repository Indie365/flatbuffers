// Code generated by the FlatBuffers compiler. DO NOT EDIT.

package generated

import (
	flatbuffers "github.com/google/flatbuffers/go"
)

type Int64T struct {
	Field int64
}

func (t *Int64T) Pack(builder *flatbuffers.Builder) flatbuffers.UOffsetT {
	if t == nil { return 0 }
	Int64Start(builder)
	Int64AddField(builder, t.Field)
	return Int64End(builder)
}

func (rcv *Int64) UnPackTo(t *Int64T) {
	t.Field = rcv.Field()
}

func (rcv *Int64) UnPack() *Int64T {
	if rcv == nil { return nil }
	t := &Int64T{}
	rcv.UnPackTo(t)
	return t
}

type Int64 struct {
	_tab flatbuffers.Table
}

func GetRootAsInt64(buf []byte, offset flatbuffers.UOffsetT) *Int64 {
	n := flatbuffers.GetUOffsetT(buf[offset:])
	x := &Int64{}
	x.Init(buf, n+offset)
	return x
}

func (rcv *Int64) Init(buf []byte, i flatbuffers.UOffsetT) {
	rcv._tab.Bytes = buf
	rcv._tab.Pos = i
}

func (rcv *Int64) Table() flatbuffers.Table {
	return rcv._tab
}

func (rcv *Int64) Field() int64 {
	o := flatbuffers.UOffsetT(rcv._tab.Offset(4))
	if o != 0 {
		return rcv._tab.GetInt64(o + rcv._tab.Pos)
	}
	return 0
}

func (rcv *Int64) MutateField(n int64) bool {
	return rcv._tab.MutateInt64Slot(4, n)
}

func Int64Start(builder *flatbuffers.Builder) {
	builder.StartObject(1)
}
func Int64AddField(builder *flatbuffers.Builder, field int64) {
	builder.PrependInt64Slot(0, field, 0)
}
func Int64End(builder *flatbuffers.Builder) flatbuffers.UOffsetT {
	return builder.EndObject()
}
