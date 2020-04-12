// Code generated by the FlatBuffers compiler. DO NOT EDIT.

package NamespaceC

import (
	flatbuffers "github.com/google/flatbuffers/go"
	NamespaceA "NamespaceA"
)

type TableInCT struct {
	ReferToA1 *NamespaceA.TableInFirstNST
	ReferToA2 *NamespaceA.SecondTableInAT
}

// TableInCT object pack function 
func (t *TableInCT) Pack(builder *flatbuffers.Builder) flatbuffers.UOffsetT {
	if t == nil {
		return 0
	}
	referToA1Offset := t.ReferToA1.Pack(builder)
	referToA2Offset := t.ReferToA2.Pack(builder)

	// pack process all field 

	TableInCStart(builder)
	TableInCAddReferToA1(builder, referToA1Offset)
	TableInCAddReferToA2(builder, referToA2Offset)
	return TableInCEnd(builder)
}

// TableInCT object unpack function
func (rcv *TableInC) UnPackTo(t *TableInCT) {
	t.ReferToA1 = rcv.ReferToA1(nil).UnPack()
	t.ReferToA2 = rcv.ReferToA2(nil).UnPack()
}

func (rcv *TableInC) UnPack() *TableInCT {
	if rcv == nil {
		return nil
	}
	t := &TableInCT{}
	rcv.UnPackTo(t)
	return t
}

type TableInC struct {
	_tab flatbuffers.Table
}

// GetRootAsTableInC shortcut to access root table
func GetRootAsTableInC(buf []byte, offset flatbuffers.UOffsetT) *TableInC {
	n := flatbuffers.GetUOffsetT(buf[offset:])
	x := &TableInC{}
	x.Init(buf, n+offset)
	return x
}

// GetTableVectorAsTableInC shortcut to access table in vector of  unions
func GetTableVectorAsTableInC(table *flatbuffers.Table) *TableInC {
	n := flatbuffers.GetUOffsetT(table.Bytes[table.Pos:])
	x := &TableInC{}
	x.Init(table.Bytes, n+table.Pos)
	return x
}

// GetTableAsTableInC shortcut to access table in single union field
func GetTableAsTableInC(table *flatbuffers.Table) *TableInC {
	x := &TableInC{}
	x.Init(table.Bytes, table.Pos)
	return x
}

func (rcv *TableInC) Init(buf []byte, i flatbuffers.UOffsetT) {
	rcv._tab.Bytes = buf
	rcv._tab.Pos = i
}

func (rcv *TableInC) Table() flatbuffers.Table {
	return rcv._tab
}

func (rcv *TableInC) ReferToA1(obj *NamespaceA.TableInFirstNS) *NamespaceA.TableInFirstNS {
	o := flatbuffers.UOffsetT(rcv._tab.Offset(4))
	if o != 0 {
		x := rcv._tab.Indirect(o + rcv._tab.Pos)
		if obj == nil {
			obj = new(NamespaceA.TableInFirstNS)
		}
		obj.Init(rcv._tab.Bytes, x)
		return obj
	}
	return nil
}

func (rcv *TableInC) ReferToA2(obj *NamespaceA.SecondTableInA) *NamespaceA.SecondTableInA {
	o := flatbuffers.UOffsetT(rcv._tab.Offset(6))
	if o != 0 {
		x := rcv._tab.Indirect(o + rcv._tab.Pos)
		if obj == nil {
			obj = new(NamespaceA.SecondTableInA)
		}
		obj.Init(rcv._tab.Bytes, x)
		return obj
	}
	return nil
}

func TableInCStart(builder *flatbuffers.Builder) {
	builder.StartObject(2)
}

func TableInCAddReferToA1(builder *flatbuffers.Builder, referToA1 flatbuffers.UOffsetT) {
	builder.PrependUOffsetTSlot(0, flatbuffers.UOffsetT(referToA1), 0)
}

func TableInCAddReferToA2(builder *flatbuffers.Builder, referToA2 flatbuffers.UOffsetT) {
	builder.PrependUOffsetTSlot(1, flatbuffers.UOffsetT(referToA2), 0)
}

func TableInCEnd(builder *flatbuffers.Builder) flatbuffers.UOffsetT {
	return builder.EndObject()
}
