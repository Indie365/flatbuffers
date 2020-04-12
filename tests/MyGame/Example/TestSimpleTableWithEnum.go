// Code generated by the FlatBuffers compiler. DO NOT EDIT.

package Example

import (
	flatbuffers "github.com/google/flatbuffers/go"
)

type TestSimpleTableWithEnumT struct {
	Color Color
}

// TestSimpleTableWithEnumT object pack function
func (t *TestSimpleTableWithEnumT) Pack(builder *flatbuffers.Builder) flatbuffers.UOffsetT {
	if t == nil {
		return 0
	}

	// pack process all field

	TestSimpleTableWithEnumStart(builder)
	TestSimpleTableWithEnumAddColor(builder, t.Color)
	return TestSimpleTableWithEnumEnd(builder)
}

// TestSimpleTableWithEnumT object unpack function
func (rcv *TestSimpleTableWithEnum) UnPackTo(t *TestSimpleTableWithEnumT) {
	t.Color = rcv.Color()
}

func (rcv *TestSimpleTableWithEnum) UnPack() *TestSimpleTableWithEnumT {
	if rcv == nil {
		return nil
	}
	t := &TestSimpleTableWithEnumT{}
	rcv.UnPackTo(t)
	return t
}

type TestSimpleTableWithEnum struct {
	_tab flatbuffers.Table
}

// GetRootAsTestSimpleTableWithEnum shortcut to access root table
func GetRootAsTestSimpleTableWithEnum(buf []byte, offset flatbuffers.UOffsetT) *TestSimpleTableWithEnum {
	n := flatbuffers.GetUOffsetT(buf[offset:])
	x := &TestSimpleTableWithEnum{}
	x.Init(buf, n+offset)
	return x
}

// GetTableVectorAsTestSimpleTableWithEnum shortcut to access table in vector of  unions
func GetTableVectorAsTestSimpleTableWithEnum(table *flatbuffers.Table) *TestSimpleTableWithEnum {
	n := flatbuffers.GetUOffsetT(table.Bytes[table.Pos:])
	x := &TestSimpleTableWithEnum{}
	x.Init(table.Bytes, n+table.Pos)
	return x
}

// GetTableAsTestSimpleTableWithEnum shortcut to access table in single union field
func GetTableAsTestSimpleTableWithEnum(table *flatbuffers.Table) *TestSimpleTableWithEnum {
	x := &TestSimpleTableWithEnum{}
	x.Init(table.Bytes, table.Pos)
	return x
}

func (rcv *TestSimpleTableWithEnum) Init(buf []byte, i flatbuffers.UOffsetT) {
	rcv._tab.Bytes = buf
	rcv._tab.Pos = i
}

func (rcv *TestSimpleTableWithEnum) Table() flatbuffers.Table {
	return rcv._tab
}

func (rcv *TestSimpleTableWithEnum) Color() Color {
	o := flatbuffers.UOffsetT(rcv._tab.Offset(4))
	if o != 0 {
		return Color(rcv._tab.GetByte(o + rcv._tab.Pos))
	}
	return 2
}

func (rcv *TestSimpleTableWithEnum) MutateColor(n Color) bool {
	return rcv._tab.MutateByteSlot(4, byte(n))
}

func TestSimpleTableWithEnumStart(builder *flatbuffers.Builder) {
	builder.StartObject(1)
}

func TestSimpleTableWithEnumAddColor(builder *flatbuffers.Builder, color Color) {
	builder.PrependByteSlot(0, byte(color), 2)
}

func TestSimpleTableWithEnumEnd(builder *flatbuffers.Builder) flatbuffers.UOffsetT {
	return builder.EndObject()
}
