from __future__ import annotations

import flatbuffers
import numpy as np

import typing
from MyGame.Example.NestedUnion.NestedUnionTest import NestedUnionTest
from MyGame.Example.NestedUnion.TestSimpleTableWithEnum import TestSimpleTableWithEnumT
from MyGame.Example.NestedUnion.Vec3 import Vec3T
from flatbuffers import table

class NestedUnionTest(object):
  @classmethod
  def GetRootAs(cls, buf: bytes, offset: int) -> NestedUnionTest: ...
  @classmethod
  def GetRootAsNestedUnionTest(cls, buf: bytes, offset: int) -> NestedUnionTest: ...
  def Init(self, buf: bytes, pos: int) -> None: ...
  def Name(self) -> typing.Optional[str]: ...
  def DataType(self) -> int: ...
  def Data(self) -> typing.Optional[table.Table]: ...
  def Id(self) -> int: ...
class NestedUnionTestT(object):
  name: typing.Optional[str]
  dataType: int
  typing.Union[None, Vec3T, TestSimpleTableWithEnumT]
  id: int
  @classmethod
  def InitFromBuf(cls, buf: bytes, pos: int) -> NestedUnionTestT: ...
  @classmethod
  def InitFromPackedBuf(cls, buf: bytes, pos: int = 0) -> NestedUnionTestT: ...
  @classmethod
  def InitFromObj(cls, nestedUnionTest: NestedUnionTest) -> NestedUnionTestT: ...
  def _UnPack(self, nestedUnionTest: NestedUnionTest) -> None: ...
  def Pack(self, builder: flatbuffers.Builder) -> None: ...

