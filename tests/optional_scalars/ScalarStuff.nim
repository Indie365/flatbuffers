#[ optional_scalars.ScalarStuff
  Automatically generated by the FlatBuffers compiler, do not modify.
  Or modify. I'm a message, not a cop.

  flatc version: 22.10.26

  Declared by  : 
  Rooting type : optional_scalars.ScalarStuff ()
]#

import OptionalByte as optional_scalars_OptionalByte
import flatbuffers
import std/options

type ScalarStuff* = object of FlatObj
func justI8*(self: ScalarStuff): int8 =
  let o = self.tab.Offset(4)
  if o != 0:
    return Get[int8](self.tab, self.tab.Pos + o)
  return 0
func `justI8=`*(self: var ScalarStuff, n: int8): bool =
  return self.tab.MutateSlot(4, n)
func maybeI8*(self: ScalarStuff): Option[int8] =
  let o = self.tab.Offset(6)
  if o != 0:
    return some(Get[int8](self.tab, self.tab.Pos + o))
func `maybeI8=`*(self: var ScalarStuff, n: Option[int8]): bool =
  return self.tab.MutateSlot(6, n)
func defaultI8*(self: ScalarStuff): int8 =
  let o = self.tab.Offset(8)
  if o != 0:
    return Get[int8](self.tab, self.tab.Pos + o)
  return 42
func `defaultI8=`*(self: var ScalarStuff, n: int8): bool =
  return self.tab.MutateSlot(8, n)
func justU8*(self: ScalarStuff): uint8 =
  let o = self.tab.Offset(10)
  if o != 0:
    return Get[uint8](self.tab, self.tab.Pos + o)
  return 0
func `justU8=`*(self: var ScalarStuff, n: uint8): bool =
  return self.tab.MutateSlot(10, n)
func maybeU8*(self: ScalarStuff): Option[uint8] =
  let o = self.tab.Offset(12)
  if o != 0:
    return some(Get[uint8](self.tab, self.tab.Pos + o))
func `maybeU8=`*(self: var ScalarStuff, n: Option[uint8]): bool =
  return self.tab.MutateSlot(12, n)
func defaultU8*(self: ScalarStuff): uint8 =
  let o = self.tab.Offset(14)
  if o != 0:
    return Get[uint8](self.tab, self.tab.Pos + o)
  return 42
func `defaultU8=`*(self: var ScalarStuff, n: uint8): bool =
  return self.tab.MutateSlot(14, n)
func justI16*(self: ScalarStuff): int16 =
  let o = self.tab.Offset(16)
  if o != 0:
    return Get[int16](self.tab, self.tab.Pos + o)
  return 0
func `justI16=`*(self: var ScalarStuff, n: int16): bool =
  return self.tab.MutateSlot(16, n)
func maybeI16*(self: ScalarStuff): Option[int16] =
  let o = self.tab.Offset(18)
  if o != 0:
    return some(Get[int16](self.tab, self.tab.Pos + o))
func `maybeI16=`*(self: var ScalarStuff, n: Option[int16]): bool =
  return self.tab.MutateSlot(18, n)
func defaultI16*(self: ScalarStuff): int16 =
  let o = self.tab.Offset(20)
  if o != 0:
    return Get[int16](self.tab, self.tab.Pos + o)
  return 42
func `defaultI16=`*(self: var ScalarStuff, n: int16): bool =
  return self.tab.MutateSlot(20, n)
func justU16*(self: ScalarStuff): uint16 =
  let o = self.tab.Offset(22)
  if o != 0:
    return Get[uint16](self.tab, self.tab.Pos + o)
  return 0
func `justU16=`*(self: var ScalarStuff, n: uint16): bool =
  return self.tab.MutateSlot(22, n)
func maybeU16*(self: ScalarStuff): Option[uint16] =
  let o = self.tab.Offset(24)
  if o != 0:
    return some(Get[uint16](self.tab, self.tab.Pos + o))
func `maybeU16=`*(self: var ScalarStuff, n: Option[uint16]): bool =
  return self.tab.MutateSlot(24, n)
func defaultU16*(self: ScalarStuff): uint16 =
  let o = self.tab.Offset(26)
  if o != 0:
    return Get[uint16](self.tab, self.tab.Pos + o)
  return 42
func `defaultU16=`*(self: var ScalarStuff, n: uint16): bool =
  return self.tab.MutateSlot(26, n)
func justI32*(self: ScalarStuff): int32 =
  let o = self.tab.Offset(28)
  if o != 0:
    return Get[int32](self.tab, self.tab.Pos + o)
  return 0
func `justI32=`*(self: var ScalarStuff, n: int32): bool =
  return self.tab.MutateSlot(28, n)
func maybeI32*(self: ScalarStuff): Option[int32] =
  let o = self.tab.Offset(30)
  if o != 0:
    return some(Get[int32](self.tab, self.tab.Pos + o))
func `maybeI32=`*(self: var ScalarStuff, n: Option[int32]): bool =
  return self.tab.MutateSlot(30, n)
func defaultI32*(self: ScalarStuff): int32 =
  let o = self.tab.Offset(32)
  if o != 0:
    return Get[int32](self.tab, self.tab.Pos + o)
  return 42
func `defaultI32=`*(self: var ScalarStuff, n: int32): bool =
  return self.tab.MutateSlot(32, n)
func justU32*(self: ScalarStuff): uint32 =
  let o = self.tab.Offset(34)
  if o != 0:
    return Get[uint32](self.tab, self.tab.Pos + o)
  return 0
func `justU32=`*(self: var ScalarStuff, n: uint32): bool =
  return self.tab.MutateSlot(34, n)
func maybeU32*(self: ScalarStuff): Option[uint32] =
  let o = self.tab.Offset(36)
  if o != 0:
    return some(Get[uint32](self.tab, self.tab.Pos + o))
func `maybeU32=`*(self: var ScalarStuff, n: Option[uint32]): bool =
  return self.tab.MutateSlot(36, n)
func defaultU32*(self: ScalarStuff): uint32 =
  let o = self.tab.Offset(38)
  if o != 0:
    return Get[uint32](self.tab, self.tab.Pos + o)
  return 42
func `defaultU32=`*(self: var ScalarStuff, n: uint32): bool =
  return self.tab.MutateSlot(38, n)
func justI64*(self: ScalarStuff): int64 =
  let o = self.tab.Offset(40)
  if o != 0:
    return Get[int64](self.tab, self.tab.Pos + o)
  return 0
func `justI64=`*(self: var ScalarStuff, n: int64): bool =
  return self.tab.MutateSlot(40, n)
func maybeI64*(self: ScalarStuff): Option[int64] =
  let o = self.tab.Offset(42)
  if o != 0:
    return some(Get[int64](self.tab, self.tab.Pos + o))
func `maybeI64=`*(self: var ScalarStuff, n: Option[int64]): bool =
  return self.tab.MutateSlot(42, n)
func defaultI64*(self: ScalarStuff): int64 =
  let o = self.tab.Offset(44)
  if o != 0:
    return Get[int64](self.tab, self.tab.Pos + o)
  return 42
func `defaultI64=`*(self: var ScalarStuff, n: int64): bool =
  return self.tab.MutateSlot(44, n)
func justU64*(self: ScalarStuff): uint64 =
  let o = self.tab.Offset(46)
  if o != 0:
    return Get[uint64](self.tab, self.tab.Pos + o)
  return 0
func `justU64=`*(self: var ScalarStuff, n: uint64): bool =
  return self.tab.MutateSlot(46, n)
func maybeU64*(self: ScalarStuff): Option[uint64] =
  let o = self.tab.Offset(48)
  if o != 0:
    return some(Get[uint64](self.tab, self.tab.Pos + o))
func `maybeU64=`*(self: var ScalarStuff, n: Option[uint64]): bool =
  return self.tab.MutateSlot(48, n)
func defaultU64*(self: ScalarStuff): uint64 =
  let o = self.tab.Offset(50)
  if o != 0:
    return Get[uint64](self.tab, self.tab.Pos + o)
  return 42
func `defaultU64=`*(self: var ScalarStuff, n: uint64): bool =
  return self.tab.MutateSlot(50, n)
func justF32*(self: ScalarStuff): float32 =
  let o = self.tab.Offset(52)
  if o != 0:
    return Get[float32](self.tab, self.tab.Pos + o)
  return 0.0
func `justF32=`*(self: var ScalarStuff, n: float32): bool =
  return self.tab.MutateSlot(52, n)
func maybeF32*(self: ScalarStuff): Option[float32] =
  let o = self.tab.Offset(54)
  if o != 0:
    return some(Get[float32](self.tab, self.tab.Pos + o))
func `maybeF32=`*(self: var ScalarStuff, n: Option[float32]): bool =
  return self.tab.MutateSlot(54, n)
func defaultF32*(self: ScalarStuff): float32 =
  let o = self.tab.Offset(56)
  if o != 0:
    return Get[float32](self.tab, self.tab.Pos + o)
  return 42.0
func `defaultF32=`*(self: var ScalarStuff, n: float32): bool =
  return self.tab.MutateSlot(56, n)
func justF64*(self: ScalarStuff): float64 =
  let o = self.tab.Offset(58)
  if o != 0:
    return Get[float64](self.tab, self.tab.Pos + o)
  return 0.0
func `justF64=`*(self: var ScalarStuff, n: float64): bool =
  return self.tab.MutateSlot(58, n)
func maybeF64*(self: ScalarStuff): Option[float64] =
  let o = self.tab.Offset(60)
  if o != 0:
    return some(Get[float64](self.tab, self.tab.Pos + o))
func `maybeF64=`*(self: var ScalarStuff, n: Option[float64]): bool =
  return self.tab.MutateSlot(60, n)
func defaultF64*(self: ScalarStuff): float64 =
  let o = self.tab.Offset(62)
  if o != 0:
    return Get[float64](self.tab, self.tab.Pos + o)
  return 42.0
func `defaultF64=`*(self: var ScalarStuff, n: float64): bool =
  return self.tab.MutateSlot(62, n)
func justBool*(self: ScalarStuff): bool =
  let o = self.tab.Offset(64)
  if o != 0:
    return Get[bool](self.tab, self.tab.Pos + o)
  return false
func `justBool=`*(self: var ScalarStuff, n: bool): bool =
  return self.tab.MutateSlot(64, n)
func maybeBool*(self: ScalarStuff): Option[bool] =
  let o = self.tab.Offset(66)
  if o != 0:
    return some(Get[bool](self.tab, self.tab.Pos + o))
func `maybeBool=`*(self: var ScalarStuff, n: Option[bool]): bool =
  return self.tab.MutateSlot(66, n)
func defaultBool*(self: ScalarStuff): bool =
  let o = self.tab.Offset(68)
  if o != 0:
    return Get[bool](self.tab, self.tab.Pos + o)
  return true
func `defaultBool=`*(self: var ScalarStuff, n: bool): bool =
  return self.tab.MutateSlot(68, n)
func justEnum*(self: ScalarStuff): optional_scalars_OptionalByte.OptionalByte =
  let o = self.tab.Offset(70)
  if o != 0:
    return optional_scalars_OptionalByte.OptionalByte(Get[int8](self.tab, self.tab.Pos + o))
  return type(result)(0)
func `justEnum=`*(self: var ScalarStuff, n: optional_scalars_OptionalByte.OptionalByte): bool =
  return self.tab.MutateSlot(70, n)
func maybeEnum*(self: ScalarStuff): Option[optional_scalars_OptionalByte.OptionalByte] =
  let o = self.tab.Offset(72)
  if o != 0:
    return some(optional_scalars_OptionalByte.OptionalByte(Get[int8](self.tab, self.tab.Pos + o)))
func `maybeEnum=`*(self: var ScalarStuff, n: Option[optional_scalars_OptionalByte.OptionalByte]): bool =
  return self.tab.MutateSlot(72, n)
func defaultEnum*(self: ScalarStuff): optional_scalars_OptionalByte.OptionalByte =
  let o = self.tab.Offset(74)
  if o != 0:
    return optional_scalars_OptionalByte.OptionalByte(Get[int8](self.tab, self.tab.Pos + o))
  return type(result)(1)
func `defaultEnum=`*(self: var ScalarStuff, n: optional_scalars_OptionalByte.OptionalByte): bool =
  return self.tab.MutateSlot(74, n)
proc ScalarStuffStart*(builder: var Builder) =
  builder.StartObject(36)
proc ScalarStuffAddjustI8*(builder: var Builder, justI8: int8) =
  builder.PrependSlot(0, justI8, default(int8))
proc ScalarStuffAddmaybeI8*(builder: var Builder, maybeI8: int8) =
  builder.PrependSlot(1, maybeI8, default(int8))
proc ScalarStuffAdddefaultI8*(builder: var Builder, defaultI8: int8) =
  builder.PrependSlot(2, defaultI8, default(int8))
proc ScalarStuffAddjustU8*(builder: var Builder, justU8: uint8) =
  builder.PrependSlot(3, justU8, default(uint8))
proc ScalarStuffAddmaybeU8*(builder: var Builder, maybeU8: uint8) =
  builder.PrependSlot(4, maybeU8, default(uint8))
proc ScalarStuffAdddefaultU8*(builder: var Builder, defaultU8: uint8) =
  builder.PrependSlot(5, defaultU8, default(uint8))
proc ScalarStuffAddjustI16*(builder: var Builder, justI16: int16) =
  builder.PrependSlot(6, justI16, default(int16))
proc ScalarStuffAddmaybeI16*(builder: var Builder, maybeI16: int16) =
  builder.PrependSlot(7, maybeI16, default(int16))
proc ScalarStuffAdddefaultI16*(builder: var Builder, defaultI16: int16) =
  builder.PrependSlot(8, defaultI16, default(int16))
proc ScalarStuffAddjustU16*(builder: var Builder, justU16: uint16) =
  builder.PrependSlot(9, justU16, default(uint16))
proc ScalarStuffAddmaybeU16*(builder: var Builder, maybeU16: uint16) =
  builder.PrependSlot(10, maybeU16, default(uint16))
proc ScalarStuffAdddefaultU16*(builder: var Builder, defaultU16: uint16) =
  builder.PrependSlot(11, defaultU16, default(uint16))
proc ScalarStuffAddjustI32*(builder: var Builder, justI32: int32) =
  builder.PrependSlot(12, justI32, default(int32))
proc ScalarStuffAddmaybeI32*(builder: var Builder, maybeI32: int32) =
  builder.PrependSlot(13, maybeI32, default(int32))
proc ScalarStuffAdddefaultI32*(builder: var Builder, defaultI32: int32) =
  builder.PrependSlot(14, defaultI32, default(int32))
proc ScalarStuffAddjustU32*(builder: var Builder, justU32: uint32) =
  builder.PrependSlot(15, justU32, default(uint32))
proc ScalarStuffAddmaybeU32*(builder: var Builder, maybeU32: uint32) =
  builder.PrependSlot(16, maybeU32, default(uint32))
proc ScalarStuffAdddefaultU32*(builder: var Builder, defaultU32: uint32) =
  builder.PrependSlot(17, defaultU32, default(uint32))
proc ScalarStuffAddjustI64*(builder: var Builder, justI64: int64) =
  builder.PrependSlot(18, justI64, default(int64))
proc ScalarStuffAddmaybeI64*(builder: var Builder, maybeI64: int64) =
  builder.PrependSlot(19, maybeI64, default(int64))
proc ScalarStuffAdddefaultI64*(builder: var Builder, defaultI64: int64) =
  builder.PrependSlot(20, defaultI64, default(int64))
proc ScalarStuffAddjustU64*(builder: var Builder, justU64: uint64) =
  builder.PrependSlot(21, justU64, default(uint64))
proc ScalarStuffAddmaybeU64*(builder: var Builder, maybeU64: uint64) =
  builder.PrependSlot(22, maybeU64, default(uint64))
proc ScalarStuffAdddefaultU64*(builder: var Builder, defaultU64: uint64) =
  builder.PrependSlot(23, defaultU64, default(uint64))
proc ScalarStuffAddjustF32*(builder: var Builder, justF32: float32) =
  builder.PrependSlot(24, justF32, default(float32))
proc ScalarStuffAddmaybeF32*(builder: var Builder, maybeF32: float32) =
  builder.PrependSlot(25, maybeF32, default(float32))
proc ScalarStuffAdddefaultF32*(builder: var Builder, defaultF32: float32) =
  builder.PrependSlot(26, defaultF32, default(float32))
proc ScalarStuffAddjustF64*(builder: var Builder, justF64: float64) =
  builder.PrependSlot(27, justF64, default(float64))
proc ScalarStuffAddmaybeF64*(builder: var Builder, maybeF64: float64) =
  builder.PrependSlot(28, maybeF64, default(float64))
proc ScalarStuffAdddefaultF64*(builder: var Builder, defaultF64: float64) =
  builder.PrependSlot(29, defaultF64, default(float64))
proc ScalarStuffAddjustBool*(builder: var Builder, justBool: bool) =
  builder.PrependSlot(30, justBool, default(bool))
proc ScalarStuffAddmaybeBool*(builder: var Builder, maybeBool: bool) =
  builder.PrependSlot(31, maybeBool, default(bool))
proc ScalarStuffAdddefaultBool*(builder: var Builder, defaultBool: bool) =
  builder.PrependSlot(32, defaultBool, default(bool))
proc ScalarStuffAddjustEnum*(builder: var Builder, justEnum: int8) =
  builder.PrependSlot(33, justEnum, default(int8))
proc ScalarStuffAddmaybeEnum*(builder: var Builder, maybeEnum: int8) =
  builder.PrependSlot(34, maybeEnum, default(int8))
proc ScalarStuffAdddefaultEnum*(builder: var Builder, defaultEnum: int8) =
  builder.PrependSlot(35, defaultEnum, default(int8))
proc ScalarStuffEnd*(builder: var Builder): uoffset =
  return builder.EndObject()
