// Code generated by the FlatBuffers compiler. DO NOT EDIT.

package NamespaceA

import (
	flatbuffers "github.com/google/flatbuffers/go"
	NamespaceC "NamespaceC"
)

type SecondTableInAT struct {
	ReferToC *NamespaceC.TableInCT
}

// SecondTableInAT object pack function 
func (t *SecondTableInAT) Pack(builder *flatbuffers.Builder) flatbuffers.UOffsetT {
	if t == nil {
		return 0
	}
	referToCOffset := t.ReferToC.Pack(builder)

	// pack process all field 

	SecondTableInAStart(builder)
	SecondTableInAAddReferToC(builder, referToCOffset)
	return SecondTableInAEnd(builder)
}

// SecondTableInAT object unpack function
func (rcv *SecondTableInA) UnPackTo(t *SecondTableInAT) {
	t.ReferToC = rcv.ReferToC(nil).UnPack()
}

func (rcv *SecondTableInA) UnPack() *SecondTableInAT {
	if rcv == nil {
		return nil
	}
	t := &SecondTableInAT{}
	rcv.UnPackTo(t)
	return t
}

type SecondTableInA struct {
	_tab flatbuffers.Table
}

// GetRootAsSecondTableInA shortcut to access root table
func GetRootAsSecondTableInA(buf []byte, offset flatbuffers.UOffsetT) *SecondTableInA {
	n := flatbuffers.GetUOffsetT(buf[offset:])
	x := &SecondTableInA{}
	x.Init(buf, n+offset)
	return x
}

// GetTableVectorAsSecondTableInA shortcut to access table in vector of  unions
func GetTableVectorAsSecondTableInA(table *flatbuffers.Table) *SecondTableInA {
	n := flatbuffers.GetUOffsetT(table.Bytes[table.Pos:])
	x := &SecondTableInA{}
	x.Init(table.Bytes, n+table.Pos)
	return x
}

// GetTableAsSecondTableInA shortcut to access table in single union field
func GetTableAsSecondTableInA(table *flatbuffers.Table) *SecondTableInA {
	x := &SecondTableInA{}
	x.Init(table.Bytes, table.Pos)
	return x
}

func (rcv *SecondTableInA) Init(buf []byte, i flatbuffers.UOffsetT) {
	rcv._tab.Bytes = buf
	rcv._tab.Pos = i
}

func (rcv *SecondTableInA) Table() flatbuffers.Table {
	return rcv._tab
}

func (rcv *SecondTableInA) ReferToC(obj *NamespaceC.TableInC) *NamespaceC.TableInC {
	o := flatbuffers.UOffsetT(rcv._tab.Offset(4))
	if o != 0 {
		x := rcv._tab.Indirect(o + rcv._tab.Pos)
		if obj == nil {
			obj = new(NamespaceC.TableInC)
		}
		obj.Init(rcv._tab.Bytes, x)
		return obj
	}
	return nil
}

func SecondTableInAStart(builder *flatbuffers.Builder) {
	builder.StartObject(1)
}

func SecondTableInAAddReferToC(builder *flatbuffers.Builder, referToC flatbuffers.UOffsetT) {
	builder.PrependUOffsetTSlot(0, flatbuffers.UOffsetT(referToC), 0)
}

func SecondTableInAEnd(builder *flatbuffers.Builder) flatbuffers.UOffsetT {
	return builder.EndObject()
}
