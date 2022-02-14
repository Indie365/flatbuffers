// Code generated by the FlatBuffers compiler. DO NOT EDIT.

package Example

import (
	flatbuffers "github.com/google/flatbuffers/go"
)

type StatT struct {
	Id string
	Val int64
	Count uint16
}

func (t *StatT) Pack(builder *flatbuffers.Builder) flatbuffers.UOffsetT {
	if t == nil { return 0 }
	idOffset := builder.CreateString(t.Id)
	StatStart(builder)
	StatAddId(builder, idOffset)
	StatAddVal(builder, t.Val)
	StatAddCount(builder, t.Count)
	return StatEnd(builder)
}

func (rcv *Stat) UnPackTo(t *StatT) {
	t.Id = string(rcv.Id())
	t.Val = rcv.Val()
	t.Count = rcv.Count()
}

func (rcv *Stat) UnPack() *StatT {
	if rcv == nil { return nil }
	t := &StatT{}
	rcv.UnPackTo(t)
	return t
}

type Stat struct {
	_tab flatbuffers.Table
}

func GetRootAsStat(buf []byte, offset flatbuffers.UOffsetT) *Stat {
	n := flatbuffers.GetUOffsetT(buf[offset:])
	x := &Stat{}
	x.Init(buf, n+offset)
	return x
}

func GetSizePrefixedRootAsStat(buf []byte, offset flatbuffers.UOffsetT) *Stat {
	n := flatbuffers.GetUOffsetT(buf[offset+flatbuffers.SizeUint32:])
	x := &Stat{}
	x.Init(buf, n+offset+flatbuffers.SizeUint32)
	return x
}

func (rcv *Stat) Init(buf []byte, i flatbuffers.UOffsetT) {
	rcv._tab.Bytes = buf
	rcv._tab.Pos = i
}

func (rcv *Stat) Table() flatbuffers.Table {
	return rcv._tab
}

func (rcv *Stat) Id() []byte {
	o := flatbuffers.UOffsetT(rcv._tab.Offset(4))
	if o != 0 {
		return rcv._tab.ByteVector(o + rcv._tab.Pos)
	}
	return nil
}

func (rcv *Stat) Val() int64 {
	o := flatbuffers.UOffsetT(rcv._tab.Offset(6))
	if o != 0 {
		return rcv._tab.GetInt64(o + rcv._tab.Pos)
	}
	return 0
}

func (rcv *Stat) MutateVal(n int64) bool {
	return rcv._tab.MutateInt64Slot(6, n)
}

func (rcv *Stat) Count() uint16 {
	o := flatbuffers.UOffsetT(rcv._tab.Offset(8))
	if o != 0 {
		return rcv._tab.GetUint16(o + rcv._tab.Pos)
	}
	return 0
}

func (rcv *Stat) MutateCount(n uint16) bool {
	return rcv._tab.MutateUint16Slot(8, n)
}

func StatStart(builder *flatbuffers.Builder) {
	builder.StartObject(3)
}
func StatAddId(builder *flatbuffers.Builder, id flatbuffers.UOffsetT) {
	builder.PrependUOffsetTSlot(0, flatbuffers.UOffsetT(id), 0)
}
func StatAddVal(builder *flatbuffers.Builder, val int64) {
	builder.PrependInt64(val)
	builder.Slot(1)
}
func StatAddCount(builder *flatbuffers.Builder, count uint16) {
	builder.PrependUint16(count)
	builder.Slot(2)
}
func StatEnd(builder *flatbuffers.Builder) flatbuffers.UOffsetT {
	return builder.EndObject()
}
