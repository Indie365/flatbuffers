// automatically generated by the FlatBuffers compiler, do not modify

namespace NamespaceC
{

using System;
using FlatBuffers;

public struct TableInC : IFlatbufferObject
{
  private Table __p;
  public ByteBuffer ByteBuffer { get { return __p.bb; } }
  public static TableInC GetRootAsTableInC(ByteBuffer _bb) { return GetRootAsTableInC(_bb, new TableInC()); }
  public static TableInC GetRootAsTableInC(ByteBuffer _bb, TableInC obj) { return (obj.__assign(_bb.GetInt(_bb.Position) + _bb.Position, _bb)); }
  public TableInC __assign(int _i, ByteBuffer _bb) { __init(_i, _bb); return this; }

  public NamespaceA.TableInFirstNS? ReferToA1 { get { int o = __p.__offset(4); return o != 0 ? (NamespaceA.TableInFirstNS?)(new NamespaceA.TableInFirstNS()).__assign(__p.__indirect(o + __p.bb_pos), __p.bb) : null; } }
  public NamespaceA.SecondTableInA? ReferToA2 { get { int o = __p.__offset(6); return o != 0 ? (NamespaceA.SecondTableInA?)(new NamespaceA.SecondTableInA()).__assign(__p.__indirect(o + __p.bb_pos), __p.bb) : null; } }

  public static Offset<TableInC> CreateTableInC(FlatBufferBuilder builder,
      Offset<NamespaceA.TableInFirstNS> refer_to_a1Offset = default(Offset<NamespaceA.TableInFirstNS>),
      Offset<NamespaceA.SecondTableInA> refer_to_a2Offset = default(Offset<NamespaceA.SecondTableInA>)) {
    builder.StartObject(2);
    TableInC.AddReferToA2(builder, refer_to_a2Offset);
    TableInC.AddReferToA1(builder, refer_to_a1Offset);
    return TableInC.EndTableInC(builder);
  }

  public static void StartTableInC(FlatBufferBuilder builder) { builder.StartObject(2); }
  public static void AddReferToA1(FlatBufferBuilder builder, Offset<NamespaceA.TableInFirstNS> referToA1Offset) { builder.AddOffset(0, referToA1Offset.Value, 0); }
  public static void AddReferToA2(FlatBufferBuilder builder, Offset<NamespaceA.SecondTableInA> referToA2Offset) { builder.AddOffset(1, referToA2Offset.Value, 0); }
  public static Offset<TableInC> EndTableInC(FlatBufferBuilder builder) {
    int o = builder.EndObject();
    return new Offset<TableInC>(o);
  }
};


}
