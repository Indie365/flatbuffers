#[ MyGame.Example.Stat
  Automatically generated by the FlatBuffers compiler, do not modify.
  Or modify. I'm a message, not a cop.

  flatc version: 22.10.26

  Declared by  : 
  Rooting type : MyGame.Example.Monster ()
]#

import flatbuffers
import std/options

type Stat* = object of FlatObj
func id*(self: Stat): Option[string] =
  let o = self.tab.Offset(4)
  if o != 0:
    return some(self.tab.String(self.tab.Pos + o))
func val*(self: Stat): int64 =
  let o = self.tab.Offset(6)
  if o != 0:
    return Get[int64](self.tab, self.tab.Pos + o)
  return 0
func `val=`*(self: var Stat, n: int64): bool =
  return self.tab.MutateSlot(6, n)
func count*(self: Stat): uint16 =
  let o = self.tab.Offset(8)
  if o != 0:
    return Get[uint16](self.tab, self.tab.Pos + o)
  return 0
func `count=`*(self: var Stat, n: uint16): bool =
  return self.tab.MutateSlot(8, n)
proc StatStart*(builder: var Builder) =
  builder.StartObject(3)
proc StatAddid*(builder: var Builder, id: uoffset) =
  builder.PrependSlot(0, id, default(uoffset))
proc StatAddval*(builder: var Builder, val: int64) =
  builder.PrependSlot(1, val, default(int64))
proc StatAddcount*(builder: var Builder, count: uint16) =
  builder.PrependSlot(2, count, default(uint16))
proc StatEnd*(builder: var Builder): uoffset =
  return builder.EndObject()
