// Code generated by the FlatBuffers compiler. DO NOT EDIT.

package NamespaceA

import (
	flatbuffers "github.com/google/flatbuffers/go"
	NamespaceA__NamespaceB "NamespaceA/NamespaceB"
)

type TableInFirstNST struct {
	FooTable *NamespaceA__NamespaceB.TableInNestedNST
	FooEnum NamespaceA__NamespaceB.EnumInNestedNS
	FooStruct *NamespaceA__NamespaceB.StructInNestedNST
}

// TableInFirstNST object pack function
func (t *TableInFirstNST) Pack(builder *flatbuffers.Builder) flatbuffers.UOffsetT {
	if t == nil {
		return 0
	}
	fooTableOffset := t.FooTable.Pack(builder)

	// pack process all field

	TableInFirstNSStart(builder)
	TableInFirstNSAddFooTable(builder, fooTableOffset)
	TableInFirstNSAddFooEnum(builder, t.FooEnum)
	fooStructOffset := t.FooStruct.Pack(builder)
	TableInFirstNSAddFooStruct(builder, fooStructOffset)
	return TableInFirstNSEnd(builder)
}

// TableInFirstNST object unpack function
func (rcv *TableInFirstNS) UnPackTo(t *TableInFirstNST) {
	t.FooTable = rcv.FooTable(nil).UnPack()
	t.FooEnum = rcv.FooEnum()
	t.FooStruct = rcv.FooStruct(nil).UnPack()
}

func (rcv *TableInFirstNS) UnPack() *TableInFirstNST {
	if rcv == nil {
		return nil
	}
	t := &TableInFirstNST{}
	rcv.UnPackTo(t)
	return t
}

type TableInFirstNS struct {
	_tab flatbuffers.Table
}

// GetRootAsTableInFirstNS shortcut to access root table
func GetRootAsTableInFirstNS(buf []byte, offset flatbuffers.UOffsetT) *TableInFirstNS {
	n := flatbuffers.GetUOffsetT(buf[offset:])
	x := &TableInFirstNS{}
	x.Init(buf, n+offset)
	return x
}

// GetTableVectorAsTableInFirstNS shortcut to access table in vector of  unions
func GetTableVectorAsTableInFirstNS(table *flatbuffers.Table) *TableInFirstNS {
	n := flatbuffers.GetUOffsetT(table.Bytes[table.Pos:])
	x := &TableInFirstNS{}
	x.Init(table.Bytes, n+table.Pos)
	return x
}

// GetTableAsTableInFirstNS shortcut to access table in single union field
func GetTableAsTableInFirstNS(table *flatbuffers.Table) *TableInFirstNS {
	x := &TableInFirstNS{}
	x.Init(table.Bytes, table.Pos)
	return x
}

func (rcv *TableInFirstNS) Init(buf []byte, i flatbuffers.UOffsetT) {
	rcv._tab.Bytes = buf
	rcv._tab.Pos = i
}

func (rcv *TableInFirstNS) Table() flatbuffers.Table {
	return rcv._tab
}

func (rcv *TableInFirstNS) FooTable(obj *NamespaceA__NamespaceB.TableInNestedNS) *NamespaceA__NamespaceB.TableInNestedNS {
	o := flatbuffers.UOffsetT(rcv._tab.Offset(4))
	if o != 0 {
		x := rcv._tab.Indirect(o + rcv._tab.Pos)
		if obj == nil {
			obj = new(NamespaceA__NamespaceB.TableInNestedNS)
		}
		obj.Init(rcv._tab.Bytes, x)
		return obj
	}
	return nil
}

func (rcv *TableInFirstNS) FooEnum() NamespaceA__NamespaceB.EnumInNestedNS {
	o := flatbuffers.UOffsetT(rcv._tab.Offset(6))
	if o != 0 {
		return NamespaceA__NamespaceB.EnumInNestedNS(rcv._tab.GetInt8(o + rcv._tab.Pos))
	}
	return 0
}

func (rcv *TableInFirstNS) MutateFooEnum(n NamespaceA__NamespaceB.EnumInNestedNS) bool {
	return rcv._tab.MutateInt8Slot(6, int8(n))
}

func (rcv *TableInFirstNS) FooStruct(obj *NamespaceA__NamespaceB.StructInNestedNS) *NamespaceA__NamespaceB.StructInNestedNS {
	o := flatbuffers.UOffsetT(rcv._tab.Offset(8))
	if o != 0 {
		x := o + rcv._tab.Pos
		if obj == nil {
			obj = new(NamespaceA__NamespaceB.StructInNestedNS)
		}
		obj.Init(rcv._tab.Bytes, x)
		return obj
	}
	return nil
}

func TableInFirstNSStart(builder *flatbuffers.Builder) {
	builder.StartObject(3)
}

func TableInFirstNSAddFooTable(builder *flatbuffers.Builder, fooTable flatbuffers.UOffsetT) {
	builder.PrependUOffsetTSlot(0, flatbuffers.UOffsetT(fooTable), 0)
}

func TableInFirstNSAddFooEnum(builder *flatbuffers.Builder, fooEnum NamespaceA__NamespaceB.EnumInNestedNS) {
	builder.PrependInt8Slot(1, int8(fooEnum), 0)
}

func TableInFirstNSAddFooStruct(builder *flatbuffers.Builder, fooStruct flatbuffers.UOffsetT) {
	builder.PrependStructSlot(2, flatbuffers.UOffsetT(fooStruct), 0)
}

func TableInFirstNSEnd(builder *flatbuffers.Builder) flatbuffers.UOffsetT {
	return builder.EndObject()
}
