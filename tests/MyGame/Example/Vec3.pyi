from __future__ import annotations

import flatbuffers
import numpy as np

import typing
from MyGame.Example.Test import Test, TestT
from MyGame.Example.Vec3 import Vec3

class Vec3(object):
  @classmethod
  def SizeOf(cls) -> int: ...

  def Init(self, buf: bytes, pos: int) -> None: ...
  def X(self) -> float: ...
  def Y(self) -> float: ...
  def Z(self) -> float: ...
  def Test1(self) -> float: ...
  def Test2(self) -> int: ...
  def Test3(self, obj: Test) -> Test: ...
class Vec3T(object):
  x: float
  y: float
  z: float
  test1: float
  test2: int
  test3: typing.Optional[TestT]
  @classmethod
  def InitFromBuf(cls, buf: bytes, pos: int) -> Vec3T: ...
  @classmethod
  def InitFromPackedBuf(cls, buf: bytes, pos: int = 0) -> Vec3T: ...
  @classmethod
  def InitFromObj(cls, vec3: Vec3) -> Vec3T: ...
  def _UnPack(self, vec3: Vec3) -> None: ...
  def Pack(self, builder: flatbuffers.Builder) -> None: ...

