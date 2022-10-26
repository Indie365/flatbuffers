#[ MyGame.Example.Monster
  Automatically generated by the FlatBuffers compiler, do not modify.
  Or modify. I'm a message, not a cop.

  flatc version: 22.10.25

  Declared by  : 
  Rooting type : MyGame.Example.Monster ()
]#

import ../InParentNamespace as MyGame_InParentNamespace
import Ability as MyGame_Example_Ability
import Any as MyGame_Example_Any
import AnyAmbiguousAliases as MyGame_Example_AnyAmbiguousAliases
import AnyUniqueAliases as MyGame_Example_AnyUniqueAliases
import Color as MyGame_Example_Color
import LongEnum as MyGame_Example_LongEnum
import Race as MyGame_Example_Race
import Referrable as MyGame_Example_Referrable
import Stat as MyGame_Example_Stat
import Test as MyGame_Example_Test
import Vec3 as MyGame_Example_Vec3
import flatbuffers
import std/options

#  an example documentation comment: "monster object"
type Monster* = object of FlatObj
func pos*(self: Monster): Option[MyGame_Example_Vec3.Vec3] =
  let o = self.tab.Offset(4)
  if o != 0:
    return some(MyGame_Example_Vec3.Vec3(tab: Vtable(Bytes: self.tab.Bytes, Pos: self.tab.Pos + o)))
func mana*(self: Monster): int16 =
  let o = self.tab.Offset(6)
  if o != 0:
    return Get[int16](self.tab, self.tab.Pos + o)
  return 150
func `mana=`*(self: var Monster, n: int16): bool =
  return self.tab.MutateSlot(6, n)
func hp*(self: Monster): int16 =
  let o = self.tab.Offset(8)
  if o != 0:
    return Get[int16](self.tab, self.tab.Pos + o)
  return 100
func `hp=`*(self: var Monster, n: int16): bool =
  return self.tab.MutateSlot(8, n)
func name*(self: Monster): string =
  let o = self.tab.Offset(10)
  if o != 0:
    return self.tab.String(self.tab.Pos + o)
  return ""
func inventoryLength*(self: Monster): int = 
  let o = self.tab.Offset(14)
  if o != 0:
    return self.tab.VectorLen(o)
func inventory*(self: Monster, j: int): uint8 = 
  let o = self.tab.Offset(14)
  if o != 0:
    var x = self.tab.Vector(o)
    x += j.uoffset * 1.uoffset
    return Get[uint8](self.tab, x)
func inventory*(self: Monster): seq[uint8] = 
  let len = self.inventoryLength
  for i in countup(0, len - 1):
    result.add(self.inventory(i))
func color*(self: Monster): MyGame_Example_Color.Color =
  let o = self.tab.Offset(16)
  if o != 0:
    return MyGame_Example_Color.Color(Get[uint8](self.tab, self.tab.Pos + o))
  return type(result)(8)
func `color=`*(self: var Monster, n: MyGame_Example_Color.Color): bool =
  return self.tab.MutateSlot(16, n)
func testType*(self: Monster): MyGame_Example_Any.Any =
  let o = self.tab.Offset(18)
  if o != 0:
    return MyGame_Example_Any.Any(Get[uint8](self.tab, self.tab.Pos + o))
  return type(result)(0)
func `testType=`*(self: var Monster, n: MyGame_Example_Any.Any): bool =
  return self.tab.MutateSlot(18, n)
func test*(self: Monster): Option[Vtable] =
  let o = self.tab.Offset(20)
  if o != 0:
    return some(self.tab.Union(o))
func test4Length*(self: Monster): int = 
  let o = self.tab.Offset(22)
  if o != 0:
    return self.tab.VectorLen(o)
func test4*(self: Monster, j: int): MyGame_Example_Test.Test = 
  let o = self.tab.Offset(22)
  if o != 0:
    var x = self.tab.Vector(o)
    x += j.uoffset * 4.uoffset
    return MyGame_Example_Test.Test(tab: Vtable(Bytes: self.tab.Bytes, Pos: x))
func test4*(self: Monster): seq[MyGame_Example_Test.Test] = 
  let len = self.test4Length
  for i in countup(0, len - 1):
    result.add(self.test4(i))
func testarrayofstringLength*(self: Monster): int = 
  let o = self.tab.Offset(24)
  if o != 0:
    return self.tab.VectorLen(o)
func testarrayofstring*(self: Monster, j: int): string = 
  let o = self.tab.Offset(24)
  if o != 0:
    var x = self.tab.Vector(o)
    x += j.uoffset * 4.uoffset
    return self.tab.String(x)
func testarrayofstring*(self: Monster): seq[string] = 
  let len = self.testarrayofstringLength
  for i in countup(0, len - 1):
    result.add(self.testarrayofstring(i))
func testarrayoftablesLength*(self: Monster): int = 
  let o = self.tab.Offset(26)
  if o != 0:
    return self.tab.VectorLen(o)
func testarrayoftables*(self: Monster, j: int): Monster = 
  let o = self.tab.Offset(26)
  if o != 0:
    var x = self.tab.Vector(o)
    x += j.uoffset * 4.uoffset
    return Monster(tab: Vtable(Bytes: self.tab.Bytes, Pos: x))
func testarrayoftables*(self: Monster): seq[Monster] = 
  let len = self.testarrayoftablesLength
  for i in countup(0, len - 1):
    result.add(self.testarrayoftables(i))
func enemy*(self: Monster): Option[Monster] =
  let o = self.tab.Offset(28)
  if o != 0:
    return some(Monster(tab: Vtable(Bytes: self.tab.Bytes, Pos: self.tab.Pos + o)))
func testnestedflatbufferLength*(self: Monster): int = 
  let o = self.tab.Offset(30)
  if o != 0:
    return self.tab.VectorLen(o)
func testnestedflatbuffer*(self: Monster, j: int): uint8 = 
  let o = self.tab.Offset(30)
  if o != 0:
    var x = self.tab.Vector(o)
    x += j.uoffset * 1.uoffset
    return Get[uint8](self.tab, x)
func testnestedflatbuffer*(self: Monster): seq[uint8] = 
  let len = self.testnestedflatbufferLength
  for i in countup(0, len - 1):
    result.add(self.testnestedflatbuffer(i))
func testempty*(self: Monster): Option[MyGame_Example_Stat.Stat] =
  let o = self.tab.Offset(32)
  if o != 0:
    return some(MyGame_Example_Stat.Stat(tab: Vtable(Bytes: self.tab.Bytes, Pos: self.tab.Pos + o)))
func testbool*(self: Monster): bool =
  let o = self.tab.Offset(34)
  if o != 0:
    return Get[bool](self.tab, self.tab.Pos + o)
  return false
func `testbool=`*(self: var Monster, n: bool): bool =
  return self.tab.MutateSlot(34, n)
func testhashs32Fnv1*(self: Monster): int32 =
  let o = self.tab.Offset(36)
  if o != 0:
    return Get[int32](self.tab, self.tab.Pos + o)
  return 0
func `testhashs32Fnv1=`*(self: var Monster, n: int32): bool =
  return self.tab.MutateSlot(36, n)
func testhashu32Fnv1*(self: Monster): uint32 =
  let o = self.tab.Offset(38)
  if o != 0:
    return Get[uint32](self.tab, self.tab.Pos + o)
  return 0
func `testhashu32Fnv1=`*(self: var Monster, n: uint32): bool =
  return self.tab.MutateSlot(38, n)
func testhashs64Fnv1*(self: Monster): int64 =
  let o = self.tab.Offset(40)
  if o != 0:
    return Get[int64](self.tab, self.tab.Pos + o)
  return 0
func `testhashs64Fnv1=`*(self: var Monster, n: int64): bool =
  return self.tab.MutateSlot(40, n)
func testhashu64Fnv1*(self: Monster): uint64 =
  let o = self.tab.Offset(42)
  if o != 0:
    return Get[uint64](self.tab, self.tab.Pos + o)
  return 0
func `testhashu64Fnv1=`*(self: var Monster, n: uint64): bool =
  return self.tab.MutateSlot(42, n)
func testhashs32Fnv1a*(self: Monster): int32 =
  let o = self.tab.Offset(44)
  if o != 0:
    return Get[int32](self.tab, self.tab.Pos + o)
  return 0
func `testhashs32Fnv1a=`*(self: var Monster, n: int32): bool =
  return self.tab.MutateSlot(44, n)
func testhashu32Fnv1a*(self: Monster): uint32 =
  let o = self.tab.Offset(46)
  if o != 0:
    return Get[uint32](self.tab, self.tab.Pos + o)
  return 0
func `testhashu32Fnv1a=`*(self: var Monster, n: uint32): bool =
  return self.tab.MutateSlot(46, n)
func testhashs64Fnv1a*(self: Monster): int64 =
  let o = self.tab.Offset(48)
  if o != 0:
    return Get[int64](self.tab, self.tab.Pos + o)
  return 0
func `testhashs64Fnv1a=`*(self: var Monster, n: int64): bool =
  return self.tab.MutateSlot(48, n)
func testhashu64Fnv1a*(self: Monster): uint64 =
  let o = self.tab.Offset(50)
  if o != 0:
    return Get[uint64](self.tab, self.tab.Pos + o)
  return 0
func `testhashu64Fnv1a=`*(self: var Monster, n: uint64): bool =
  return self.tab.MutateSlot(50, n)
func testarrayofboolsLength*(self: Monster): int = 
  let o = self.tab.Offset(52)
  if o != 0:
    return self.tab.VectorLen(o)
func testarrayofbools*(self: Monster, j: int): bool = 
  let o = self.tab.Offset(52)
  if o != 0:
    var x = self.tab.Vector(o)
    x += j.uoffset * 1.uoffset
    return Get[bool](self.tab, x)
func testarrayofbools*(self: Monster): seq[bool] = 
  let len = self.testarrayofboolsLength
  for i in countup(0, len - 1):
    result.add(self.testarrayofbools(i))
func testf*(self: Monster): float32 =
  let o = self.tab.Offset(54)
  if o != 0:
    return Get[float32](self.tab, self.tab.Pos + o)
  return 3.14159
func `testf=`*(self: var Monster, n: float32): bool =
  return self.tab.MutateSlot(54, n)
func testf2*(self: Monster): float32 =
  let o = self.tab.Offset(56)
  if o != 0:
    return Get[float32](self.tab, self.tab.Pos + o)
  return 3.0
func `testf2=`*(self: var Monster, n: float32): bool =
  return self.tab.MutateSlot(56, n)
func testf3*(self: Monster): float32 =
  let o = self.tab.Offset(58)
  if o != 0:
    return Get[float32](self.tab, self.tab.Pos + o)
  return 0.0
func `testf3=`*(self: var Monster, n: float32): bool =
  return self.tab.MutateSlot(58, n)
func testarrayofstring2Length*(self: Monster): int = 
  let o = self.tab.Offset(60)
  if o != 0:
    return self.tab.VectorLen(o)
func testarrayofstring2*(self: Monster, j: int): string = 
  let o = self.tab.Offset(60)
  if o != 0:
    var x = self.tab.Vector(o)
    x += j.uoffset * 4.uoffset
    return self.tab.String(x)
func testarrayofstring2*(self: Monster): seq[string] = 
  let len = self.testarrayofstring2Length
  for i in countup(0, len - 1):
    result.add(self.testarrayofstring2(i))
func testarrayofsortedstructLength*(self: Monster): int = 
  let o = self.tab.Offset(62)
  if o != 0:
    return self.tab.VectorLen(o)
func testarrayofsortedstruct*(self: Monster, j: int): MyGame_Example_Ability.Ability = 
  let o = self.tab.Offset(62)
  if o != 0:
    var x = self.tab.Vector(o)
    x += j.uoffset * 8.uoffset
    return MyGame_Example_Ability.Ability(tab: Vtable(Bytes: self.tab.Bytes, Pos: x))
func testarrayofsortedstruct*(self: Monster): seq[MyGame_Example_Ability.Ability] = 
  let len = self.testarrayofsortedstructLength
  for i in countup(0, len - 1):
    result.add(self.testarrayofsortedstruct(i))
func flexLength*(self: Monster): int = 
  let o = self.tab.Offset(64)
  if o != 0:
    return self.tab.VectorLen(o)
func flex*(self: Monster, j: int): uint8 = 
  let o = self.tab.Offset(64)
  if o != 0:
    var x = self.tab.Vector(o)
    x += j.uoffset * 1.uoffset
    return Get[uint8](self.tab, x)
func flex*(self: Monster): seq[uint8] = 
  let len = self.flexLength
  for i in countup(0, len - 1):
    result.add(self.flex(i))
func test5Length*(self: Monster): int = 
  let o = self.tab.Offset(66)
  if o != 0:
    return self.tab.VectorLen(o)
func test5*(self: Monster, j: int): MyGame_Example_Test.Test = 
  let o = self.tab.Offset(66)
  if o != 0:
    var x = self.tab.Vector(o)
    x += j.uoffset * 4.uoffset
    return MyGame_Example_Test.Test(tab: Vtable(Bytes: self.tab.Bytes, Pos: x))
func test5*(self: Monster): seq[MyGame_Example_Test.Test] = 
  let len = self.test5Length
  for i in countup(0, len - 1):
    result.add(self.test5(i))
func vectorOfLongsLength*(self: Monster): int = 
  let o = self.tab.Offset(68)
  if o != 0:
    return self.tab.VectorLen(o)
func vectorOfLongs*(self: Monster, j: int): int64 = 
  let o = self.tab.Offset(68)
  if o != 0:
    var x = self.tab.Vector(o)
    x += j.uoffset * 8.uoffset
    return Get[int64](self.tab, x)
func vectorOfLongs*(self: Monster): seq[int64] = 
  let len = self.vectorOfLongsLength
  for i in countup(0, len - 1):
    result.add(self.vectorOfLongs(i))
func vectorOfDoublesLength*(self: Monster): int = 
  let o = self.tab.Offset(70)
  if o != 0:
    return self.tab.VectorLen(o)
func vectorOfDoubles*(self: Monster, j: int): float64 = 
  let o = self.tab.Offset(70)
  if o != 0:
    var x = self.tab.Vector(o)
    x += j.uoffset * 8.uoffset
    return Get[float64](self.tab, x)
func vectorOfDoubles*(self: Monster): seq[float64] = 
  let len = self.vectorOfDoublesLength
  for i in countup(0, len - 1):
    result.add(self.vectorOfDoubles(i))
func parentNamespaceTest*(self: Monster): Option[MyGame_InParentNamespace.InParentNamespace] =
  let o = self.tab.Offset(72)
  if o != 0:
    return some(MyGame_InParentNamespace.InParentNamespace(tab: Vtable(Bytes: self.tab.Bytes, Pos: self.tab.Pos + o)))
func vectorOfReferrablesLength*(self: Monster): int = 
  let o = self.tab.Offset(74)
  if o != 0:
    return self.tab.VectorLen(o)
func vectorOfReferrables*(self: Monster, j: int): MyGame_Example_Referrable.Referrable = 
  let o = self.tab.Offset(74)
  if o != 0:
    var x = self.tab.Vector(o)
    x += j.uoffset * 4.uoffset
    return MyGame_Example_Referrable.Referrable(tab: Vtable(Bytes: self.tab.Bytes, Pos: x))
func vectorOfReferrables*(self: Monster): seq[MyGame_Example_Referrable.Referrable] = 
  let len = self.vectorOfReferrablesLength
  for i in countup(0, len - 1):
    result.add(self.vectorOfReferrables(i))
func singleWeakReference*(self: Monster): uint64 =
  let o = self.tab.Offset(76)
  if o != 0:
    return Get[uint64](self.tab, self.tab.Pos + o)
  return 0
func `singleWeakReference=`*(self: var Monster, n: uint64): bool =
  return self.tab.MutateSlot(76, n)
func vectorOfWeakReferencesLength*(self: Monster): int = 
  let o = self.tab.Offset(78)
  if o != 0:
    return self.tab.VectorLen(o)
func vectorOfWeakReferences*(self: Monster, j: int): uint64 = 
  let o = self.tab.Offset(78)
  if o != 0:
    var x = self.tab.Vector(o)
    x += j.uoffset * 8.uoffset
    return Get[uint64](self.tab, x)
func vectorOfWeakReferences*(self: Monster): seq[uint64] = 
  let len = self.vectorOfWeakReferencesLength
  for i in countup(0, len - 1):
    result.add(self.vectorOfWeakReferences(i))
func vectorOfStrongReferrablesLength*(self: Monster): int = 
  let o = self.tab.Offset(80)
  if o != 0:
    return self.tab.VectorLen(o)
func vectorOfStrongReferrables*(self: Monster, j: int): MyGame_Example_Referrable.Referrable = 
  let o = self.tab.Offset(80)
  if o != 0:
    var x = self.tab.Vector(o)
    x += j.uoffset * 4.uoffset
    return MyGame_Example_Referrable.Referrable(tab: Vtable(Bytes: self.tab.Bytes, Pos: x))
func vectorOfStrongReferrables*(self: Monster): seq[MyGame_Example_Referrable.Referrable] = 
  let len = self.vectorOfStrongReferrablesLength
  for i in countup(0, len - 1):
    result.add(self.vectorOfStrongReferrables(i))
func coOwningReference*(self: Monster): uint64 =
  let o = self.tab.Offset(82)
  if o != 0:
    return Get[uint64](self.tab, self.tab.Pos + o)
  return 0
func `coOwningReference=`*(self: var Monster, n: uint64): bool =
  return self.tab.MutateSlot(82, n)
func vectorOfCoOwningReferencesLength*(self: Monster): int = 
  let o = self.tab.Offset(84)
  if o != 0:
    return self.tab.VectorLen(o)
func vectorOfCoOwningReferences*(self: Monster, j: int): uint64 = 
  let o = self.tab.Offset(84)
  if o != 0:
    var x = self.tab.Vector(o)
    x += j.uoffset * 8.uoffset
    return Get[uint64](self.tab, x)
func vectorOfCoOwningReferences*(self: Monster): seq[uint64] = 
  let len = self.vectorOfCoOwningReferencesLength
  for i in countup(0, len - 1):
    result.add(self.vectorOfCoOwningReferences(i))
func nonOwningReference*(self: Monster): uint64 =
  let o = self.tab.Offset(86)
  if o != 0:
    return Get[uint64](self.tab, self.tab.Pos + o)
  return 0
func `nonOwningReference=`*(self: var Monster, n: uint64): bool =
  return self.tab.MutateSlot(86, n)
func vectorOfNonOwningReferencesLength*(self: Monster): int = 
  let o = self.tab.Offset(88)
  if o != 0:
    return self.tab.VectorLen(o)
func vectorOfNonOwningReferences*(self: Monster, j: int): uint64 = 
  let o = self.tab.Offset(88)
  if o != 0:
    var x = self.tab.Vector(o)
    x += j.uoffset * 8.uoffset
    return Get[uint64](self.tab, x)
func vectorOfNonOwningReferences*(self: Monster): seq[uint64] = 
  let len = self.vectorOfNonOwningReferencesLength
  for i in countup(0, len - 1):
    result.add(self.vectorOfNonOwningReferences(i))
func anyUniqueType*(self: Monster): MyGame_Example_AnyUniqueAliases.AnyUniqueAliases =
  let o = self.tab.Offset(90)
  if o != 0:
    return MyGame_Example_AnyUniqueAliases.AnyUniqueAliases(Get[uint8](self.tab, self.tab.Pos + o))
  return type(result)(0)
func `anyUniqueType=`*(self: var Monster, n: MyGame_Example_AnyUniqueAliases.AnyUniqueAliases): bool =
  return self.tab.MutateSlot(90, n)
func anyUnique*(self: Monster): Option[Vtable] =
  let o = self.tab.Offset(92)
  if o != 0:
    return some(self.tab.Union(o))
func anyAmbiguousType*(self: Monster): MyGame_Example_AnyAmbiguousAliases.AnyAmbiguousAliases =
  let o = self.tab.Offset(94)
  if o != 0:
    return MyGame_Example_AnyAmbiguousAliases.AnyAmbiguousAliases(Get[uint8](self.tab, self.tab.Pos + o))
  return type(result)(0)
func `anyAmbiguousType=`*(self: var Monster, n: MyGame_Example_AnyAmbiguousAliases.AnyAmbiguousAliases): bool =
  return self.tab.MutateSlot(94, n)
func anyAmbiguous*(self: Monster): Option[Vtable] =
  let o = self.tab.Offset(96)
  if o != 0:
    return some(self.tab.Union(o))
func vectorOfEnumsLength*(self: Monster): int = 
  let o = self.tab.Offset(98)
  if o != 0:
    return self.tab.VectorLen(o)
func vectorOfEnums*(self: Monster, j: int): MyGame_Example_Color.Color = 
  let o = self.tab.Offset(98)
  if o != 0:
    var x = self.tab.Vector(o)
    x += j.uoffset * 1.uoffset
    return MyGame_Example_Color.Color(Get[uint8](self.tab, x))
func vectorOfEnums*(self: Monster): seq[MyGame_Example_Color.Color] = 
  let len = self.vectorOfEnumsLength
  for i in countup(0, len - 1):
    result.add(self.vectorOfEnums(i))
func signedEnum*(self: Monster): MyGame_Example_Race.Race =
  let o = self.tab.Offset(100)
  if o != 0:
    return MyGame_Example_Race.Race(Get[int8](self.tab, self.tab.Pos + o))
  return type(result)(-1)
func `signedEnum=`*(self: var Monster, n: MyGame_Example_Race.Race): bool =
  return self.tab.MutateSlot(100, n)
func testrequirednestedflatbufferLength*(self: Monster): int = 
  let o = self.tab.Offset(102)
  if o != 0:
    return self.tab.VectorLen(o)
func testrequirednestedflatbuffer*(self: Monster, j: int): uint8 = 
  let o = self.tab.Offset(102)
  if o != 0:
    var x = self.tab.Vector(o)
    x += j.uoffset * 1.uoffset
    return Get[uint8](self.tab, x)
func testrequirednestedflatbuffer*(self: Monster): seq[uint8] = 
  let len = self.testrequirednestedflatbufferLength
  for i in countup(0, len - 1):
    result.add(self.testrequirednestedflatbuffer(i))
func scalarKeySortedTablesLength*(self: Monster): int = 
  let o = self.tab.Offset(104)
  if o != 0:
    return self.tab.VectorLen(o)
func scalarKeySortedTables*(self: Monster, j: int): MyGame_Example_Stat.Stat = 
  let o = self.tab.Offset(104)
  if o != 0:
    var x = self.tab.Vector(o)
    x += j.uoffset * 4.uoffset
    return MyGame_Example_Stat.Stat(tab: Vtable(Bytes: self.tab.Bytes, Pos: x))
func scalarKeySortedTables*(self: Monster): seq[MyGame_Example_Stat.Stat] = 
  let len = self.scalarKeySortedTablesLength
  for i in countup(0, len - 1):
    result.add(self.scalarKeySortedTables(i))
func nativeInline*(self: Monster): Option[MyGame_Example_Test.Test] =
  let o = self.tab.Offset(106)
  if o != 0:
    return some(MyGame_Example_Test.Test(tab: Vtable(Bytes: self.tab.Bytes, Pos: self.tab.Pos + o)))
func longEnumNonEnumDefault*(self: Monster): MyGame_Example_LongEnum.LongEnum =
  let o = self.tab.Offset(108)
  if o != 0:
    return MyGame_Example_LongEnum.LongEnum(Get[uint64](self.tab, self.tab.Pos + o))
  return type(result)(0)
func `longEnumNonEnumDefault=`*(self: var Monster, n: MyGame_Example_LongEnum.LongEnum): bool =
  return self.tab.MutateSlot(108, n)
func longEnumNormalDefault*(self: Monster): MyGame_Example_LongEnum.LongEnum =
  let o = self.tab.Offset(110)
  if o != 0:
    return MyGame_Example_LongEnum.LongEnum(Get[uint64](self.tab, self.tab.Pos + o))
  return type(result)(2)
func `longEnumNormalDefault=`*(self: var Monster, n: MyGame_Example_LongEnum.LongEnum): bool =
  return self.tab.MutateSlot(110, n)
func nanDefault*(self: Monster): float32 =
  let o = self.tab.Offset(112)
  if o != 0:
    return Get[float32](self.tab, self.tab.Pos + o)
  return NaN
func `nanDefault=`*(self: var Monster, n: float32): bool =
  return self.tab.MutateSlot(112, n)
func infDefault*(self: Monster): float32 =
  let o = self.tab.Offset(114)
  if o != 0:
    return Get[float32](self.tab, self.tab.Pos + o)
  return Inf
func `infDefault=`*(self: var Monster, n: float32): bool =
  return self.tab.MutateSlot(114, n)
func positiveInfDefault*(self: Monster): float32 =
  let o = self.tab.Offset(116)
  if o != 0:
    return Get[float32](self.tab, self.tab.Pos + o)
  return Inf
func `positiveInfDefault=`*(self: var Monster, n: float32): bool =
  return self.tab.MutateSlot(116, n)
func infinityDefault*(self: Monster): float32 =
  let o = self.tab.Offset(118)
  if o != 0:
    return Get[float32](self.tab, self.tab.Pos + o)
  return Inf
func `infinityDefault=`*(self: var Monster, n: float32): bool =
  return self.tab.MutateSlot(118, n)
func positiveInfinityDefault*(self: Monster): float32 =
  let o = self.tab.Offset(120)
  if o != 0:
    return Get[float32](self.tab, self.tab.Pos + o)
  return Inf
func `positiveInfinityDefault=`*(self: var Monster, n: float32): bool =
  return self.tab.MutateSlot(120, n)
func negativeInfDefault*(self: Monster): float32 =
  let o = self.tab.Offset(122)
  if o != 0:
    return Get[float32](self.tab, self.tab.Pos + o)
  return -Inf
func `negativeInfDefault=`*(self: var Monster, n: float32): bool =
  return self.tab.MutateSlot(122, n)
func negativeInfinityDefault*(self: Monster): float32 =
  let o = self.tab.Offset(124)
  if o != 0:
    return Get[float32](self.tab, self.tab.Pos + o)
  return -Inf
func `negativeInfinityDefault=`*(self: var Monster, n: float32): bool =
  return self.tab.MutateSlot(124, n)
func doubleInfDefault*(self: Monster): float64 =
  let o = self.tab.Offset(126)
  if o != 0:
    return Get[float64](self.tab, self.tab.Pos + o)
  return Inf
func `doubleInfDefault=`*(self: var Monster, n: float64): bool =
  return self.tab.MutateSlot(126, n)
proc MonsterStart*(builder: var Builder) =
  builder.StartObject(62)
proc MonsterAddpos*(builder: var Builder, pos: uoffset) =
  builder.PrependStructSlot(0, pos, default(uoffset))
proc MonsterAddmana*(builder: var Builder, mana: int16) =
  builder.PrependSlot(1, mana, default(int16))
proc MonsterAddhp*(builder: var Builder, hp: int16) =
  builder.PrependSlot(2, hp, default(int16))
proc MonsterAddname*(builder: var Builder, name: uoffset) =
  builder.PrependSlot(3, name, default(uoffset))
proc MonsterAddinventory*(builder: var Builder, inventory: uoffset) =
  builder.PrependSlot(5, inventory, default(uoffset))
proc MonsterStartinventoryVector*(builder: var Builder, numElems: uoffset) =
  builder.StartVector(1, numElems, 1)
proc MonsterAddcolor*(builder: var Builder, color: uint8) =
  builder.PrependSlot(6, color, default(uint8))
proc MonsterAddtestType*(builder: var Builder, testType: uint8) =
  builder.PrependSlot(7, testType, default(uint8))
proc MonsterAddtest*(builder: var Builder, test: uoffset) =
  builder.PrependSlot(8, test, default(uoffset))
proc MonsterAddtest4*(builder: var Builder, test4: uoffset) =
  builder.PrependSlot(9, test4, default(uoffset))
proc MonsterStarttest4Vector*(builder: var Builder, numElems: uoffset) =
  builder.StartVector(4, numElems, 2)
proc MonsterAddtestarrayofstring*(builder: var Builder, testarrayofstring: uoffset) =
  builder.PrependSlot(10, testarrayofstring, default(uoffset))
proc MonsterStarttestarrayofstringVector*(builder: var Builder, numElems: uoffset) =
  builder.StartVector(4, numElems, 4)
proc MonsterAddtestarrayoftables*(builder: var Builder, testarrayoftables: uoffset) =
  builder.PrependSlot(11, testarrayoftables, default(uoffset))
proc MonsterStarttestarrayoftablesVector*(builder: var Builder, numElems: uoffset) =
  builder.StartVector(4, numElems, 4)
proc MonsterAddenemy*(builder: var Builder, enemy: uoffset) =
  builder.PrependStructSlot(12, enemy, default(uoffset))
proc MonsterAddtestnestedflatbuffer*(builder: var Builder, testnestedflatbuffer: uoffset) =
  builder.PrependSlot(13, testnestedflatbuffer, default(uoffset))
proc MonsterStarttestnestedflatbufferVector*(builder: var Builder, numElems: uoffset) =
  builder.StartVector(1, numElems, 1)
proc MonsterAddtestempty*(builder: var Builder, testempty: uoffset) =
  builder.PrependStructSlot(14, testempty, default(uoffset))
proc MonsterAddtestbool*(builder: var Builder, testbool: bool) =
  builder.PrependSlot(15, testbool, default(bool))
proc MonsterAddtesthashs32Fnv1*(builder: var Builder, testhashs32Fnv1: int32) =
  builder.PrependSlot(16, testhashs32Fnv1, default(int32))
proc MonsterAddtesthashu32Fnv1*(builder: var Builder, testhashu32Fnv1: uint32) =
  builder.PrependSlot(17, testhashu32Fnv1, default(uint32))
proc MonsterAddtesthashs64Fnv1*(builder: var Builder, testhashs64Fnv1: int64) =
  builder.PrependSlot(18, testhashs64Fnv1, default(int64))
proc MonsterAddtesthashu64Fnv1*(builder: var Builder, testhashu64Fnv1: uint64) =
  builder.PrependSlot(19, testhashu64Fnv1, default(uint64))
proc MonsterAddtesthashs32Fnv1a*(builder: var Builder, testhashs32Fnv1a: int32) =
  builder.PrependSlot(20, testhashs32Fnv1a, default(int32))
proc MonsterAddtesthashu32Fnv1a*(builder: var Builder, testhashu32Fnv1a: uint32) =
  builder.PrependSlot(21, testhashu32Fnv1a, default(uint32))
proc MonsterAddtesthashs64Fnv1a*(builder: var Builder, testhashs64Fnv1a: int64) =
  builder.PrependSlot(22, testhashs64Fnv1a, default(int64))
proc MonsterAddtesthashu64Fnv1a*(builder: var Builder, testhashu64Fnv1a: uint64) =
  builder.PrependSlot(23, testhashu64Fnv1a, default(uint64))
proc MonsterAddtestarrayofbools*(builder: var Builder, testarrayofbools: uoffset) =
  builder.PrependSlot(24, testarrayofbools, default(uoffset))
proc MonsterStarttestarrayofboolsVector*(builder: var Builder, numElems: uoffset) =
  builder.StartVector(1, numElems, 1)
proc MonsterAddtestf*(builder: var Builder, testf: float32) =
  builder.PrependSlot(25, testf, default(float32))
proc MonsterAddtestf2*(builder: var Builder, testf2: float32) =
  builder.PrependSlot(26, testf2, default(float32))
proc MonsterAddtestf3*(builder: var Builder, testf3: float32) =
  builder.PrependSlot(27, testf3, default(float32))
proc MonsterAddtestarrayofstring2*(builder: var Builder, testarrayofstring2: uoffset) =
  builder.PrependSlot(28, testarrayofstring2, default(uoffset))
proc MonsterStarttestarrayofstring2Vector*(builder: var Builder, numElems: uoffset) =
  builder.StartVector(4, numElems, 4)
proc MonsterAddtestarrayofsortedstruct*(builder: var Builder, testarrayofsortedstruct: uoffset) =
  builder.PrependSlot(29, testarrayofsortedstruct, default(uoffset))
proc MonsterStarttestarrayofsortedstructVector*(builder: var Builder, numElems: uoffset) =
  builder.StartVector(8, numElems, 4)
proc MonsterAddflex*(builder: var Builder, flex: uoffset) =
  builder.PrependSlot(30, flex, default(uoffset))
proc MonsterStartflexVector*(builder: var Builder, numElems: uoffset) =
  builder.StartVector(1, numElems, 1)
proc MonsterAddtest5*(builder: var Builder, test5: uoffset) =
  builder.PrependSlot(31, test5, default(uoffset))
proc MonsterStarttest5Vector*(builder: var Builder, numElems: uoffset) =
  builder.StartVector(4, numElems, 2)
proc MonsterAddvectorOfLongs*(builder: var Builder, vectorOfLongs: uoffset) =
  builder.PrependSlot(32, vectorOfLongs, default(uoffset))
proc MonsterStartvectorOfLongsVector*(builder: var Builder, numElems: uoffset) =
  builder.StartVector(8, numElems, 8)
proc MonsterAddvectorOfDoubles*(builder: var Builder, vectorOfDoubles: uoffset) =
  builder.PrependSlot(33, vectorOfDoubles, default(uoffset))
proc MonsterStartvectorOfDoublesVector*(builder: var Builder, numElems: uoffset) =
  builder.StartVector(8, numElems, 8)
proc MonsterAddparentNamespaceTest*(builder: var Builder, parentNamespaceTest: uoffset) =
  builder.PrependStructSlot(34, parentNamespaceTest, default(uoffset))
proc MonsterAddvectorOfReferrables*(builder: var Builder, vectorOfReferrables: uoffset) =
  builder.PrependSlot(35, vectorOfReferrables, default(uoffset))
proc MonsterStartvectorOfReferrablesVector*(builder: var Builder, numElems: uoffset) =
  builder.StartVector(4, numElems, 4)
proc MonsterAddsingleWeakReference*(builder: var Builder, singleWeakReference: uint64) =
  builder.PrependSlot(36, singleWeakReference, default(uint64))
proc MonsterAddvectorOfWeakReferences*(builder: var Builder, vectorOfWeakReferences: uoffset) =
  builder.PrependSlot(37, vectorOfWeakReferences, default(uoffset))
proc MonsterStartvectorOfWeakReferencesVector*(builder: var Builder, numElems: uoffset) =
  builder.StartVector(8, numElems, 8)
proc MonsterAddvectorOfStrongReferrables*(builder: var Builder, vectorOfStrongReferrables: uoffset) =
  builder.PrependSlot(38, vectorOfStrongReferrables, default(uoffset))
proc MonsterStartvectorOfStrongReferrablesVector*(builder: var Builder, numElems: uoffset) =
  builder.StartVector(4, numElems, 4)
proc MonsterAddcoOwningReference*(builder: var Builder, coOwningReference: uint64) =
  builder.PrependSlot(39, coOwningReference, default(uint64))
proc MonsterAddvectorOfCoOwningReferences*(builder: var Builder, vectorOfCoOwningReferences: uoffset) =
  builder.PrependSlot(40, vectorOfCoOwningReferences, default(uoffset))
proc MonsterStartvectorOfCoOwningReferencesVector*(builder: var Builder, numElems: uoffset) =
  builder.StartVector(8, numElems, 8)
proc MonsterAddnonOwningReference*(builder: var Builder, nonOwningReference: uint64) =
  builder.PrependSlot(41, nonOwningReference, default(uint64))
proc MonsterAddvectorOfNonOwningReferences*(builder: var Builder, vectorOfNonOwningReferences: uoffset) =
  builder.PrependSlot(42, vectorOfNonOwningReferences, default(uoffset))
proc MonsterStartvectorOfNonOwningReferencesVector*(builder: var Builder, numElems: uoffset) =
  builder.StartVector(8, numElems, 8)
proc MonsterAddanyUniqueType*(builder: var Builder, anyUniqueType: uint8) =
  builder.PrependSlot(43, anyUniqueType, default(uint8))
proc MonsterAddanyUnique*(builder: var Builder, anyUnique: uoffset) =
  builder.PrependSlot(44, anyUnique, default(uoffset))
proc MonsterAddanyAmbiguousType*(builder: var Builder, anyAmbiguousType: uint8) =
  builder.PrependSlot(45, anyAmbiguousType, default(uint8))
proc MonsterAddanyAmbiguous*(builder: var Builder, anyAmbiguous: uoffset) =
  builder.PrependSlot(46, anyAmbiguous, default(uoffset))
proc MonsterAddvectorOfEnums*(builder: var Builder, vectorOfEnums: uoffset) =
  builder.PrependSlot(47, vectorOfEnums, default(uoffset))
proc MonsterStartvectorOfEnumsVector*(builder: var Builder, numElems: uoffset) =
  builder.StartVector(1, numElems, 1)
proc MonsterAddsignedEnum*(builder: var Builder, signedEnum: int8) =
  builder.PrependSlot(48, signedEnum, default(int8))
proc MonsterAddtestrequirednestedflatbuffer*(builder: var Builder, testrequirednestedflatbuffer: uoffset) =
  builder.PrependSlot(49, testrequirednestedflatbuffer, default(uoffset))
proc MonsterStarttestrequirednestedflatbufferVector*(builder: var Builder, numElems: uoffset) =
  builder.StartVector(1, numElems, 1)
proc MonsterAddscalarKeySortedTables*(builder: var Builder, scalarKeySortedTables: uoffset) =
  builder.PrependSlot(50, scalarKeySortedTables, default(uoffset))
proc MonsterStartscalarKeySortedTablesVector*(builder: var Builder, numElems: uoffset) =
  builder.StartVector(4, numElems, 4)
proc MonsterAddnativeInline*(builder: var Builder, nativeInline: uoffset) =
  builder.PrependStructSlot(51, nativeInline, default(uoffset))
proc MonsterAddlongEnumNonEnumDefault*(builder: var Builder, longEnumNonEnumDefault: uint64) =
  builder.PrependSlot(52, longEnumNonEnumDefault, default(uint64))
proc MonsterAddlongEnumNormalDefault*(builder: var Builder, longEnumNormalDefault: uint64) =
  builder.PrependSlot(53, longEnumNormalDefault, default(uint64))
proc MonsterAddnanDefault*(builder: var Builder, nanDefault: float32) =
  builder.PrependSlot(54, nanDefault, default(float32))
proc MonsterAddinfDefault*(builder: var Builder, infDefault: float32) =
  builder.PrependSlot(55, infDefault, default(float32))
proc MonsterAddpositiveInfDefault*(builder: var Builder, positiveInfDefault: float32) =
  builder.PrependSlot(56, positiveInfDefault, default(float32))
proc MonsterAddinfinityDefault*(builder: var Builder, infinityDefault: float32) =
  builder.PrependSlot(57, infinityDefault, default(float32))
proc MonsterAddpositiveInfinityDefault*(builder: var Builder, positiveInfinityDefault: float32) =
  builder.PrependSlot(58, positiveInfinityDefault, default(float32))
proc MonsterAddnegativeInfDefault*(builder: var Builder, negativeInfDefault: float32) =
  builder.PrependSlot(59, negativeInfDefault, default(float32))
proc MonsterAddnegativeInfinityDefault*(builder: var Builder, negativeInfinityDefault: float32) =
  builder.PrependSlot(60, negativeInfinityDefault, default(float32))
proc MonsterAdddoubleInfDefault*(builder: var Builder, doubleInfDefault: float64) =
  builder.PrependSlot(61, doubleInfDefault, default(float64))
proc MonsterEnd*(builder: var Builder): uoffset =
  return builder.EndObject()
