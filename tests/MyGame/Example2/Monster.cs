// automatically generated by the FlatBuffers compiler, do not modify

namespace MyGame.Example2
{

using System;
using FlatBuffers;

public struct Monster : IFlatbufferObject
{
  private Table __p;
  public ByteBuffer ByteBuffer { get { return __p.bb; } }
  public static Monster GetRootAsMonster(ByteBuffer _bb) { return GetRootAsMonster(_bb, new Monster()); }
  public static Monster GetRootAsMonster(ByteBuffer _bb, Monster obj) { return (obj.__assign(_bb.GetInt(_bb.Position) + _bb.Position, _bb)); }
  public Monster __assign(int _i, ByteBuffer _bb) { __init(_i, _bb); return this; }


  public static void StartMonster(FlatBufferBuilder builder) { builder.StartObject(0); }
  public static Offset<Monster> EndMonster(FlatBufferBuilder builder) {
    int o = builder.EndObject();
    return new Offset<Monster>(o);
  }
};


}
