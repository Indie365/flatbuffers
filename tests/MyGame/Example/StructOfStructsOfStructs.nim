#[ MyGame.Example.StructOfStructsOfStructs
  Automatically generated by the FlatBuffers compiler, do not modify.
  Or modify. I'm a message, not a cop.

  flatc version: 22.11.22

  Declared by  : 
  Rooting type : MyGame.Example.Monster ()
]#

import StructOfStructs as MyGame_Example_StructOfStructs
import flatbuffers

type StructOfStructsOfStructs* = object of FlatObj
func a*(self: StructOfStructsOfStructs): MyGame_Example_StructOfStructs.StructOfStructs =
  return MyGame_Example_StructOfStructs.StructOfStructs(tab: Vtable(Bytes: self.tab.Bytes, Pos: self.tab.Pos + 0))
proc StructOfStructsOfStructsCreate*(self: var Builder, a_a_id: uint32, a_a_distance: uint32, a_b_a: int16, a_b_b: int8, a_c_id: uint32, a_c_distance: uint32): uoffset =
  self.Prep(4, 20)
  self.Prep(4, 20)
  self.Prep(4, 8)
  self.Prepend(a_c_distance)
  self.Prepend(a_c_id)
  self.Prep(2, 4)
  self.Pad(1)
  self.Prepend(a_b_b)
  self.Prepend(a_b_a)
  self.Prep(4, 8)
  self.Prepend(a_a_distance)
  self.Prepend(a_a_id)
  return self.Offset()
