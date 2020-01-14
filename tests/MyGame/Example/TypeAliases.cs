// <auto-generated>
//  automatically generated by the FlatBuffers compiler, do not modify
// </auto-generated>

namespace MyGame.Example
{

using global::System;
using global::System.Collections.Generic;
using global::System.Linq;
using global::FlatBuffers;

public struct TypeAliases : IFlatbufferObject
{
  private Table __p;
  public ByteBuffer ByteBuffer { get { return __p.bb; } }
  public static void ValidateVersion() { FlatBufferConstants.FLATBUFFERS_1_11_1(); }
  public static TypeAliases GetRootAsTypeAliases(ByteBuffer _bb) { return GetRootAsTypeAliases(_bb, new TypeAliases()); }
  public static TypeAliases GetRootAsTypeAliases(ByteBuffer _bb, TypeAliases obj) { return (obj.__assign(_bb.GetInt(_bb.Position) + _bb.Position, _bb)); }
  public void __init(int _i, ByteBuffer _bb) { __p = new Table(_i, _bb); }
  public TypeAliases __assign(int _i, ByteBuffer _bb) { __init(_i, _bb); return this; }

  public sbyte I8 { get { int o = __p.__offset(4); return o != 0 ? __p.bb.GetSbyte(o + __p.bb_pos) : (sbyte)0; } }
  public bool MutateI8(sbyte i8) { int o = __p.__offset(4); if (o != 0) { __p.bb.PutSbyte(o + __p.bb_pos, i8); return true; } else { return false; } }
  public byte U8 { get { int o = __p.__offset(6); return o != 0 ? __p.bb.Get(o + __p.bb_pos) : (byte)0; } }
  public bool MutateU8(byte u8) { int o = __p.__offset(6); if (o != 0) { __p.bb.Put(o + __p.bb_pos, u8); return true; } else { return false; } }
  public short I16 { get { int o = __p.__offset(8); return o != 0 ? __p.bb.GetShort(o + __p.bb_pos) : (short)0; } }
  public bool MutateI16(short i16) { int o = __p.__offset(8); if (o != 0) { __p.bb.PutShort(o + __p.bb_pos, i16); return true; } else { return false; } }
  public ushort U16 { get { int o = __p.__offset(10); return o != 0 ? __p.bb.GetUshort(o + __p.bb_pos) : (ushort)0; } }
  public bool MutateU16(ushort u16) { int o = __p.__offset(10); if (o != 0) { __p.bb.PutUshort(o + __p.bb_pos, u16); return true; } else { return false; } }
  public int I32 { get { int o = __p.__offset(12); return o != 0 ? __p.bb.GetInt(o + __p.bb_pos) : (int)0; } }
  public bool MutateI32(int i32) { int o = __p.__offset(12); if (o != 0) { __p.bb.PutInt(o + __p.bb_pos, i32); return true; } else { return false; } }
  public uint U32 { get { int o = __p.__offset(14); return o != 0 ? __p.bb.GetUint(o + __p.bb_pos) : (uint)0; } }
  public bool MutateU32(uint u32) { int o = __p.__offset(14); if (o != 0) { __p.bb.PutUint(o + __p.bb_pos, u32); return true; } else { return false; } }
  public long I64 { get { int o = __p.__offset(16); return o != 0 ? __p.bb.GetLong(o + __p.bb_pos) : (long)0; } }
  public bool MutateI64(long i64) { int o = __p.__offset(16); if (o != 0) { __p.bb.PutLong(o + __p.bb_pos, i64); return true; } else { return false; } }
  public ulong U64 { get { int o = __p.__offset(18); return o != 0 ? __p.bb.GetUlong(o + __p.bb_pos) : (ulong)0; } }
  public bool MutateU64(ulong u64) { int o = __p.__offset(18); if (o != 0) { __p.bb.PutUlong(o + __p.bb_pos, u64); return true; } else { return false; } }
  public float F32 { get { int o = __p.__offset(20); return o != 0 ? __p.bb.GetFloat(o + __p.bb_pos) : (float)0.0f; } }
  public bool MutateF32(float f32) { int o = __p.__offset(20); if (o != 0) { __p.bb.PutFloat(o + __p.bb_pos, f32); return true; } else { return false; } }
  public double F64 { get { int o = __p.__offset(22); return o != 0 ? __p.bb.GetDouble(o + __p.bb_pos) : (double)0.0; } }
  public bool MutateF64(double f64) { int o = __p.__offset(22); if (o != 0) { __p.bb.PutDouble(o + __p.bb_pos, f64); return true; } else { return false; } }
  public sbyte V8(int j) { int o = __p.__offset(24); return o != 0 ? __p.bb.GetSbyte(__p.__vector(o) + j * 1) : (sbyte)0; }
  public int V8Length { get { int o = __p.__offset(24); return o != 0 ? __p.__vector_len(o) : 0; } }
#if ENABLE_SPAN_T
  public Span<sbyte> GetV8Bytes() { return __p.__vector_as_span<sbyte>(24, 1); }
#else
  public ArraySegment<byte>? GetV8Bytes() { return __p.__vector_as_arraysegment(24); }
#endif
  public sbyte[] GetV8Array() { return __p.__vector_as_array<sbyte>(24); }
  public bool MutateV8(int j, sbyte v8) { int o = __p.__offset(24); if (o != 0) { __p.bb.PutSbyte(__p.__vector(o) + j * 1, v8); return true; } else { return false; } }
  public double Vf64(int j) { int o = __p.__offset(26); return o != 0 ? __p.bb.GetDouble(__p.__vector(o) + j * 8) : (double)0; }
  public int Vf64Length { get { int o = __p.__offset(26); return o != 0 ? __p.__vector_len(o) : 0; } }
#if ENABLE_SPAN_T
  public Span<double> GetVf64Bytes() { return __p.__vector_as_span<double>(26, 8); }
#else
  public ArraySegment<byte>? GetVf64Bytes() { return __p.__vector_as_arraysegment(26); }
#endif
  public double[] GetVf64Array() { return __p.__vector_as_array<double>(26); }
  public bool MutateVf64(int j, double vf64) { int o = __p.__offset(26); if (o != 0) { __p.bb.PutDouble(__p.__vector(o) + j * 8, vf64); return true; } else { return false; } }

  public static Offset<MyGame.Example.TypeAliases> CreateTypeAliases(FlatBufferBuilder builder,
      sbyte i8 = 0,
      byte u8 = 0,
      short i16 = 0,
      ushort u16 = 0,
      int i32 = 0,
      uint u32 = 0,
      long i64 = 0,
      ulong u64 = 0,
      float f32 = 0.0f,
      double f64 = 0.0,
      VectorOffset v8Offset = default(VectorOffset),
      VectorOffset vf64Offset = default(VectorOffset)) {
    builder.StartTable(12);
    TypeAliases.AddF64(builder, f64);
    TypeAliases.AddU64(builder, u64);
    TypeAliases.AddI64(builder, i64);
    TypeAliases.AddVf64(builder, vf64Offset);
    TypeAliases.AddV8(builder, v8Offset);
    TypeAliases.AddF32(builder, f32);
    TypeAliases.AddU32(builder, u32);
    TypeAliases.AddI32(builder, i32);
    TypeAliases.AddU16(builder, u16);
    TypeAliases.AddI16(builder, i16);
    TypeAliases.AddU8(builder, u8);
    TypeAliases.AddI8(builder, i8);
    return TypeAliases.EndTypeAliases(builder);
  }

  public static void StartTypeAliases(FlatBufferBuilder builder) { builder.StartTable(12); }
  public static void AddI8(FlatBufferBuilder builder, sbyte i8) { builder.AddSbyte(0, i8, 0); }
  public static void AddU8(FlatBufferBuilder builder, byte u8) { builder.AddByte(1, u8, 0); }
  public static void AddI16(FlatBufferBuilder builder, short i16) { builder.AddShort(2, i16, 0); }
  public static void AddU16(FlatBufferBuilder builder, ushort u16) { builder.AddUshort(3, u16, 0); }
  public static void AddI32(FlatBufferBuilder builder, int i32) { builder.AddInt(4, i32, 0); }
  public static void AddU32(FlatBufferBuilder builder, uint u32) { builder.AddUint(5, u32, 0); }
  public static void AddI64(FlatBufferBuilder builder, long i64) { builder.AddLong(6, i64, 0); }
  public static void AddU64(FlatBufferBuilder builder, ulong u64) { builder.AddUlong(7, u64, 0); }
  public static void AddF32(FlatBufferBuilder builder, float f32) { builder.AddFloat(8, f32, 0.0f); }
  public static void AddF64(FlatBufferBuilder builder, double f64) { builder.AddDouble(9, f64, 0.0); }
  public static void AddV8(FlatBufferBuilder builder, VectorOffset v8Offset) { builder.AddOffset(10, v8Offset.Value, 0); }
  public static VectorOffset CreateV8Vector(FlatBufferBuilder builder, sbyte[] data) { builder.StartVector(1, data.Length, 1); for (int i = data.Length - 1; i >= 0; i--) builder.AddSbyte(data[i]); return builder.EndVector(); }
  public static VectorOffset CreateV8VectorBlock(FlatBufferBuilder builder, sbyte[] data) { builder.StartVector(1, data.Length, 1); builder.Add(data); return builder.EndVector(); }
  public static void StartV8Vector(FlatBufferBuilder builder, int numElems) { builder.StartVector(1, numElems, 1); }
  public static void AddVf64(FlatBufferBuilder builder, VectorOffset vf64Offset) { builder.AddOffset(11, vf64Offset.Value, 0); }
  public static VectorOffset CreateVf64Vector(FlatBufferBuilder builder, double[] data) { builder.StartVector(8, data.Length, 8); for (int i = data.Length - 1; i >= 0; i--) builder.AddDouble(data[i]); return builder.EndVector(); }
  public static VectorOffset CreateVf64VectorBlock(FlatBufferBuilder builder, double[] data) { builder.StartVector(8, data.Length, 8); builder.Add(data); return builder.EndVector(); }
  public static void StartVf64Vector(FlatBufferBuilder builder, int numElems) { builder.StartVector(8, numElems, 8); }
  public static Offset<MyGame.Example.TypeAliases> EndTypeAliases(FlatBufferBuilder builder) {
    int o = builder.EndTable();
    return new Offset<MyGame.Example.TypeAliases>(o);
  }
  public TypeAliasesT UnPack() {
    var _o = new TypeAliasesT();
    this.UnPackTo(_o);
    return _o;
  }
  public void UnPackTo(TypeAliasesT _o) {
    _o.I8 = this.I8;
    _o.U8 = this.U8;
    _o.I16 = this.I16;
    _o.U16 = this.U16;
    _o.I32 = this.I32;
    _o.U32 = this.U32;
    _o.I64 = this.I64;
    _o.U64 = this.U64;
    _o.F32 = this.F32;
    _o.F64 = this.F64;
    _o.V8 = new List<sbyte>();
    for (var _j = 0; _j < this.V8Length; ++_j) { _o.V8.Add(this.V8(_j)); }
    _o.Vf64 = new List<double>();
    for (var _j = 0; _j < this.Vf64Length; ++_j) { _o.Vf64.Add(this.Vf64(_j)); }
  }
  public static Offset<MyGame.Example.TypeAliases> Pack(FlatBufferBuilder builder, TypeAliasesT _o) {
    if (_o == null) return default(Offset<MyGame.Example.TypeAliases>);
    var _v8 = _o.V8 == null ? default(VectorOffset) : CreateV8Vector(builder, _o.V8.ToArray());
    var _vf64 = _o.Vf64 == null ? default(VectorOffset) : CreateVf64Vector(builder, _o.Vf64.ToArray());
    return CreateTypeAliases(
      builder,
      _o.I8,
      _o.U8,
      _o.I16,
      _o.U16,
      _o.I32,
      _o.U32,
      _o.I64,
      _o.U64,
      _o.F32,
      _o.F64,
      _v8,
      _vf64);
  }
};

public class TypeAliasesT
{
  public sbyte I8 { get; set; } = 0;
  public byte U8 { get; set; } = 0;
  public short I16 { get; set; } = 0;
  public ushort U16 { get; set; } = 0;
  public int I32 { get; set; } = 0;
  public uint U32 { get; set; } = 0;
  public long I64 { get; set; } = 0;
  public ulong U64 { get; set; } = 0;
  public float F32 { get; set; } = 0.0f;
  public double F64 { get; set; } = 0.0;
  public List<sbyte> V8 { get; set; } 
  public List<double> Vf64 { get; set; } 
};


}
