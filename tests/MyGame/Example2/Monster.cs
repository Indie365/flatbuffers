// <auto-generated>
//  automatically generated by the FlatBuffers compiler, do not modify
// </auto-generated>

namespace MyGame.Example2
{

using global::System;
using global::FlatBuffers;

public struct Monster : IFlatbufferObject
{
  private Table __p;
  public ByteBuffer ByteBuffer { get { return __p.bb; } }
  public static Monster GetRootAsMonster(ByteBuffer _bb) { return GetRootAsMonster(_bb, new Monster()); }
  public static Monster GetSizePrefixedRootAsMonster(ByteBuffer _bb) { return GetSizePrefixedRootAsMonster(_bb, new Monster()); }
  public static Monster GetRootAsMonster(ByteBuffer _bb, Monster obj) { return (obj.__assign(_bb.GetInt(_bb.Position) + _bb.Position, _bb)); }
  public static Monster GetSizePrefixedRootAsMonster(ByteBuffer _bb, Monster obj) { ByteBuffer __bb = _bb.Slice(); __bb.Position = FlatBufferConstants.SizePrefixLength; return GetRootAsMonster(__bb, obj); }
  public static int GetSizePrefix(ByteBuffer _bb) { return _bb.GetInt(_bb.Position); }
  public void __init(int _i, ByteBuffer _bb) { __p.bb_pos = _i; __p.bb = _bb; }
  public Monster __assign(int _i, ByteBuffer _bb) { __init(_i, _bb); return this; }


  public static void StartMonster(FlatBufferBuilder builder) { builder.StartObject(0); }
  public static Offset<Monster> EndMonster(FlatBufferBuilder builder) {
    int o = builder.EndObject();
    return new Offset<Monster>(o);
  }
};


}
