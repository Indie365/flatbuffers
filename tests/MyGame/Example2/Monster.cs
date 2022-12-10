// <auto-generated>
//  automatically generated by the FlatBuffers compiler, do not modify
// </auto-generated>

namespace MyGame.Example2
{

using global::System;
using global::System.Collections.Generic;
using global::Google.FlatBuffers;

public struct Monster : IFlatbufferObject
{
  private Table __p;
  public ByteBuffer ByteBuffer { get { return __p.bb; } }
  public static void ValidateVersion() { FlatBufferConstants.FLATBUFFERS_22_12_06(); }
  public static Monster GetRootAsMonster(ByteBuffer _bb) { return GetRootAsMonster(_bb, new Monster()); }
  public static Monster GetRootAsMonster(ByteBuffer _bb, Monster obj) { return (obj.__assign(_bb.GetInt(_bb.Position) + _bb.Position, _bb)); }
  public void __init(int _i, ByteBuffer _bb) { __p = new Table(_i, _bb); }
  public Monster __assign(int _i, ByteBuffer _bb) { __init(_i, _bb); return this; }


  public static void StartMonster(FlatBufferBuilder builder) { builder.StartTable(0); }
  public static Offset<MyGame.Example2.Monster> EndMonster(FlatBufferBuilder builder) {
    int o = builder.EndTable();
    return new Offset<MyGame.Example2.Monster>(o);
  }
  public MonsterT UnPack() {
    var _o = new MonsterT();
    this.UnPackTo(_o);
    return _o;
  }
  public void UnPackTo(MonsterT _o) {
  }
  public static Offset<MyGame.Example2.Monster> Pack(FlatBufferBuilder builder, MonsterT _o) {
    if (_o == null) return default(Offset<MyGame.Example2.Monster>);
    StartMonster(builder);
    return EndMonster(builder);
  }
}

public class MonsterT
{

  public MonsterT() {
  }
}


}
