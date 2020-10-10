// Code generated by the FlatBuffers compiler. DO NOT EDIT.

package Example

import (
	flatbuffers "github.com/google/flatbuffers/go"
)

type TypeAliasesT struct {
	I8   int8
	U8   byte
	I16  int16
	U16  uint16
	I32  int32
	U32  uint32
	I64  int64
	U64  uint64
	F32  float32
	F64  float64
	V8   []int8
	Vf64 []float64
}

func (t *TypeAliasesT) Pack(builder *flatbuffers.Builder) flatbuffers.UOffsetT {
	if t == nil {
		return 0
	}
	v8Offset := flatbuffers.UOffsetT(0)
	if t.V8 != nil {
		v8Length := len(t.V8)
		TypeAliasesStartV8Vector(builder, v8Length)
		for j := v8Length - 1; j >= 0; j-- {
			builder.PrependInt8(t.V8[j])
		}
		v8Offset = builder.EndVector(v8Length)
	}
	vf64Offset := flatbuffers.UOffsetT(0)
	if t.Vf64 != nil {
		vf64Length := len(t.Vf64)
		TypeAliasesStartVf64Vector(builder, vf64Length)
		for j := vf64Length - 1; j >= 0; j-- {
			builder.PrependFloat64(t.Vf64[j])
		}
		vf64Offset = builder.EndVector(vf64Length)
	}
	TypeAliasesStart(builder)
	TypeAliasesAddI8(builder, t.I8)
	TypeAliasesAddU8(builder, t.U8)
	TypeAliasesAddI16(builder, t.I16)
	TypeAliasesAddU16(builder, t.U16)
	TypeAliasesAddI32(builder, t.I32)
	TypeAliasesAddU32(builder, t.U32)
	TypeAliasesAddI64(builder, t.I64)
	TypeAliasesAddU64(builder, t.U64)
	TypeAliasesAddF32(builder, t.F32)
	TypeAliasesAddF64(builder, t.F64)
	TypeAliasesAddV8(builder, v8Offset)
	TypeAliasesAddVf64(builder, vf64Offset)
	return TypeAliasesEnd(builder)
}

func (rcv *TypeAliases) UnPackTo(t *TypeAliasesT) {
	t.I8 = rcv.I8()
	t.U8 = rcv.U8()
	t.I16 = rcv.I16()
	t.U16 = rcv.U16()
	t.I32 = rcv.I32()
	t.U32 = rcv.U32()
	t.I64 = rcv.I64()
	t.U64 = rcv.U64()
	t.F32 = rcv.F32()
	t.F64 = rcv.F64()
	v8Length := rcv.V8Length()
	t.V8 = make([]int8, v8Length)
	for j := 0; j < v8Length; j++ {
		t.V8[j] = rcv.V8(j)
	}
	vf64Length := rcv.Vf64Length()
	t.Vf64 = make([]float64, vf64Length)
	for j := 0; j < vf64Length; j++ {
		t.Vf64[j] = rcv.Vf64(j)
	}
}

func (rcv *TypeAliases) UnPack() *TypeAliasesT {
	if rcv == nil {
		return nil
	}
	t := &TypeAliasesT{}
	rcv.UnPackTo(t)
	return t
}

type TypeAliases struct {
	_tab flatbuffers.Table
}

func GetRootAsTypeAliases(buf []byte, offset flatbuffers.UOffsetT) *TypeAliases {
	n := flatbuffers.GetUOffsetT(buf[offset:])
	x := &TypeAliases{}
	x.Init(buf, n+offset)
	return x
}

func (rcv *TypeAliases) Init(buf []byte, i flatbuffers.UOffsetT) {
	rcv._tab.Bytes = buf
	rcv._tab.Pos = i
}

func (rcv *TypeAliases) Table() flatbuffers.Table {
	return rcv._tab
}

func (rcv *TypeAliases) I8() int8 {
	o := flatbuffers.UOffsetT(rcv._tab.Offset(4))
	if o != 0 {
		return rcv._tab.GetInt8(o + rcv._tab.Pos)
	}
	return 0
}

func (rcv *TypeAliases) MutateI8(n int8) bool {
	return rcv._tab.MutateInt8Slot(4, n)
}

func (rcv *TypeAliases) U8() byte {
	o := flatbuffers.UOffsetT(rcv._tab.Offset(6))
	if o != 0 {
		return rcv._tab.GetByte(o + rcv._tab.Pos)
	}
	return 0
}

func (rcv *TypeAliases) MutateU8(n byte) bool {
	return rcv._tab.MutateByteSlot(6, n)
}

func (rcv *TypeAliases) I16() int16 {
	o := flatbuffers.UOffsetT(rcv._tab.Offset(8))
	if o != 0 {
		return rcv._tab.GetInt16(o + rcv._tab.Pos)
	}
	return 0
}

func (rcv *TypeAliases) MutateI16(n int16) bool {
	return rcv._tab.MutateInt16Slot(8, n)
}

func (rcv *TypeAliases) U16() uint16 {
	o := flatbuffers.UOffsetT(rcv._tab.Offset(10))
	if o != 0 {
		return rcv._tab.GetUint16(o + rcv._tab.Pos)
	}
	return 0
}

func (rcv *TypeAliases) MutateU16(n uint16) bool {
	return rcv._tab.MutateUint16Slot(10, n)
}

func (rcv *TypeAliases) I32() int32 {
	o := flatbuffers.UOffsetT(rcv._tab.Offset(12))
	if o != 0 {
		return rcv._tab.GetInt32(o + rcv._tab.Pos)
	}
	return 0
}

func (rcv *TypeAliases) MutateI32(n int32) bool {
	return rcv._tab.MutateInt32Slot(12, n)
}

func (rcv *TypeAliases) U32() uint32 {
	o := flatbuffers.UOffsetT(rcv._tab.Offset(14))
	if o != 0 {
		return rcv._tab.GetUint32(o + rcv._tab.Pos)
	}
	return 0
}

func (rcv *TypeAliases) MutateU32(n uint32) bool {
	return rcv._tab.MutateUint32Slot(14, n)
}

func (rcv *TypeAliases) I64() int64 {
	o := flatbuffers.UOffsetT(rcv._tab.Offset(16))
	if o != 0 {
		return rcv._tab.GetInt64(o + rcv._tab.Pos)
	}
	return 0
}

func (rcv *TypeAliases) MutateI64(n int64) bool {
	return rcv._tab.MutateInt64Slot(16, n)
}

func (rcv *TypeAliases) U64() uint64 {
	o := flatbuffers.UOffsetT(rcv._tab.Offset(18))
	if o != 0 {
		return rcv._tab.GetUint64(o + rcv._tab.Pos)
	}
	return 0
}

func (rcv *TypeAliases) MutateU64(n uint64) bool {
	return rcv._tab.MutateUint64Slot(18, n)
}

func (rcv *TypeAliases) F32() float32 {
	o := flatbuffers.UOffsetT(rcv._tab.Offset(20))
	if o != 0 {
		return rcv._tab.GetFloat32(o + rcv._tab.Pos)
	}
	return 0.0
}

func (rcv *TypeAliases) MutateF32(n float32) bool {
	return rcv._tab.MutateFloat32Slot(20, n)
}

func (rcv *TypeAliases) F64() float64 {
	o := flatbuffers.UOffsetT(rcv._tab.Offset(22))
	if o != 0 {
		return rcv._tab.GetFloat64(o + rcv._tab.Pos)
	}
	return 0.0
}

func (rcv *TypeAliases) MutateF64(n float64) bool {
	return rcv._tab.MutateFloat64Slot(22, n)
}

func (rcv *TypeAliases) V8(j int) int8 {
	o := flatbuffers.UOffsetT(rcv._tab.Offset(24))
	if o != 0 {
		a := rcv._tab.Vector(o)
		return rcv._tab.GetInt8(a + flatbuffers.UOffsetT(j*1))
	}
	return 0
}

func (rcv *TypeAliases) V8Length() int {
	o := flatbuffers.UOffsetT(rcv._tab.Offset(24))
	if o != 0 {
		return rcv._tab.VectorLen(o)
	}
	return 0
}

func (rcv *TypeAliases) MutateV8(j int, n int8) bool {
	o := flatbuffers.UOffsetT(rcv._tab.Offset(24))
	if o != 0 {
		a := rcv._tab.Vector(o)
		return rcv._tab.MutateInt8(a+flatbuffers.UOffsetT(j*1), n)
	}
	return false
}

func (rcv *TypeAliases) Vf64(j int) float64 {
	o := flatbuffers.UOffsetT(rcv._tab.Offset(26))
	if o != 0 {
		a := rcv._tab.Vector(o)
		return rcv._tab.GetFloat64(a + flatbuffers.UOffsetT(j*8))
	}
	return 0
}

func (rcv *TypeAliases) Vf64Length() int {
	o := flatbuffers.UOffsetT(rcv._tab.Offset(26))
	if o != 0 {
		return rcv._tab.VectorLen(o)
	}
	return 0
}

func (rcv *TypeAliases) MutateVf64(j int, n float64) bool {
	o := flatbuffers.UOffsetT(rcv._tab.Offset(26))
	if o != 0 {
		a := rcv._tab.Vector(o)
		return rcv._tab.MutateFloat64(a+flatbuffers.UOffsetT(j*8), n)
	}
	return false
}

func TypeAliasesStart(builder *flatbuffers.Builder) {
	builder.StartObject(12)
}
func TypeAliasesAddI8(builder *flatbuffers.Builder, i8 int8) {
	builder.PrependInt8Slot(0, i8, 0)
}
func TypeAliasesAddU8(builder *flatbuffers.Builder, u8 byte) {
	builder.PrependByteSlot(1, u8, 0)
}
func TypeAliasesAddI16(builder *flatbuffers.Builder, i16 int16) {
	builder.PrependInt16Slot(2, i16, 0)
}
func TypeAliasesAddU16(builder *flatbuffers.Builder, u16 uint16) {
	builder.PrependUint16Slot(3, u16, 0)
}
func TypeAliasesAddI32(builder *flatbuffers.Builder, i32 int32) {
	builder.PrependInt32Slot(4, i32, 0)
}
func TypeAliasesAddU32(builder *flatbuffers.Builder, u32 uint32) {
	builder.PrependUint32Slot(5, u32, 0)
}
func TypeAliasesAddI64(builder *flatbuffers.Builder, i64 int64) {
	builder.PrependInt64Slot(6, i64, 0)
}
func TypeAliasesAddU64(builder *flatbuffers.Builder, u64 uint64) {
	builder.PrependUint64Slot(7, u64, 0)
}
func TypeAliasesAddF32(builder *flatbuffers.Builder, f32 float32) {
	builder.PrependFloat32Slot(8, f32, 0.0)
}
func TypeAliasesAddF64(builder *flatbuffers.Builder, f64 float64) {
	builder.PrependFloat64Slot(9, f64, 0.0)
}
func TypeAliasesAddV8(builder *flatbuffers.Builder, v8 flatbuffers.UOffsetT) {
	builder.PrependUOffsetTSlot(10, flatbuffers.UOffsetT(v8), 0)
}
func TypeAliasesStartV8Vector(builder *flatbuffers.Builder, numElems int) flatbuffers.UOffsetT {
	return builder.StartVector(1, numElems, 1)
}
func TypeAliasesAddVf64(builder *flatbuffers.Builder, vf64 flatbuffers.UOffsetT) {
	builder.PrependUOffsetTSlot(11, flatbuffers.UOffsetT(vf64), 0)
}
func TypeAliasesStartVf64Vector(builder *flatbuffers.Builder, numElems int) flatbuffers.UOffsetT {
	return builder.StartVector(8, numElems, 8)
}
func TypeAliasesEnd(builder *flatbuffers.Builder) flatbuffers.UOffsetT {
	return builder.EndObject()
}
