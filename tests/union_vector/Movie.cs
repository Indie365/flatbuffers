// <auto-generated>
//  automatically generated by the FlatBuffers compiler, do not modify
// </auto-generated>

using global::System;
using global::FlatBuffers;

public struct Movie : IFlatbufferObject
{
  private Table __p;
  public ByteBuffer ByteBuffer { get { return __p.bb; } }
  public static void ValidateVersion() { FlatBufferConstants.FLATBUFFERS_1_11_1(); }
  public static Movie GetRootAsMovie(ByteBuffer _bb) { return GetRootAsMovie(_bb, new Movie()); }
  public static Movie GetRootAsMovie(ByteBuffer _bb, Movie obj) { return (obj.__assign(_bb.GetInt(_bb.Position) + _bb.Position, _bb)); }
  public static bool MovieBufferHasIdentifier(ByteBuffer _bb) { return Table.__has_identifier(_bb, "MOVI"); }
  public void __init(int _i, ByteBuffer _bb) { __p = new Table(_i, _bb); }
  public Movie __assign(int _i, ByteBuffer _bb) { __init(_i, _bb); return this; }

  public Character MainCharacterType { get { int o = __p.__offset(4); return o != 0 ? (Character)__p.bb.Get(o + __p.bb_pos) : Character.NONE; } }
  public bool MutateMainCharacterType(Character main_character_type) { int o = __p.__offset(4); if (o != 0) { __p.bb.Put(o + __p.bb_pos, (byte)main_character_type); return true; } else { return false; } }
  public TTable? MainCharacter<TTable>() where TTable : struct, IFlatbufferObject { int o = __p.__offset(6); return o != 0 ? (TTable?)__p.__union<TTable>(o + __p.bb_pos) : null; }
  public Character CharactersType(int j) { int o = __p.__offset(8); return o != 0 ? (Character)__p.bb.Get(__p.__vector(o) + j * 1) : (Character)0; }
  public int CharactersTypeLength { get { int o = __p.__offset(8); return o != 0 ? __p.__vector_len(o) : 0; } }
#if ENABLE_SPAN_T
  public Span<Character> GetCharactersTypeBytes() { return __p.__vector_as_span<Character>(8, 1); }
#else
  public ArraySegment<byte>? GetCharactersTypeBytes() { return __p.__vector_as_arraysegment(8); }
#endif
  public Character[] GetCharactersTypeArray() { int o = __p.__offset(8); if (o == 0) return null; int p = __p.__vector(o); int l = __p.__vector_len(o); Character[] a = new Character[l]; for (int i = 0; i < l; i++) { a[i] = (Character)__p.bb.Get(p + i * 1); } return a; }
  public bool MutateCharactersType(int j, Character characters_type) { int o = __p.__offset(8); if (o != 0) { __p.bb.Put(__p.__vector(o) + j * 1, (byte)characters_type); return true; } else { return false; } }
  public TTable? Characters<TTable>(int j) where TTable : struct, IFlatbufferObject { int o = __p.__offset(10); return o != 0 ? (TTable?)__p.__union<TTable>(__p.__vector(o) + j * 4) : null; }
  public int CharactersLength { get { int o = __p.__offset(10); return o != 0 ? __p.__vector_len(o) : 0; } }

  public static Offset<Movie> CreateMovie(FlatBufferBuilder builder,
      Character main_character_type = Character.NONE,
      int main_characterOffset = 0,
      VectorOffset characters_typeOffset = default(VectorOffset),
      VectorOffset charactersOffset = default(VectorOffset)) {
    builder.StartTable(4);
    Movie.AddCharacters(builder, charactersOffset);
    Movie.AddCharactersType(builder, characters_typeOffset);
    Movie.AddMainCharacter(builder, main_characterOffset);
    Movie.AddMainCharacterType(builder, main_character_type);
    return Movie.EndMovie(builder);
  }

  public static void StartMovie(FlatBufferBuilder builder) { builder.StartTable(4); }
  public static void AddMainCharacterType(FlatBufferBuilder builder, Character mainCharacterType) { builder.AddByte(0, (byte)mainCharacterType, 0); }
  public static void AddMainCharacter(FlatBufferBuilder builder, int mainCharacterOffset) { builder.AddOffset(1, mainCharacterOffset, 0); }
  public static void AddCharactersType(FlatBufferBuilder builder, VectorOffset charactersTypeOffset) { builder.AddOffset(2, charactersTypeOffset.Value, 0); }
  public static VectorOffset CreateCharactersTypeVector(FlatBufferBuilder builder, Character[] data) { builder.StartVector(1, data.Length, 1); for (int i = data.Length - 1; i >= 0; i--) builder.AddByte((byte)data[i]); return builder.EndVector(); }
  public static void StartCharactersTypeVector(FlatBufferBuilder builder, int numElems) { builder.StartVector(1, numElems, 1); }
  public static void AddCharacters(FlatBufferBuilder builder, VectorOffset charactersOffset) { builder.AddOffset(3, charactersOffset.Value, 0); }
  public static VectorOffset CreateCharactersVector(FlatBufferBuilder builder, int[] data) { builder.StartVector(4, data.Length, 4); for (int i = data.Length - 1; i >= 0; i--) builder.AddOffset(data[i]); return builder.EndVector(); }
  public static VectorOffset CreateCharactersVectorBlock(FlatBufferBuilder builder, int[] data) { builder.StartVector(4, data.Length, 4); builder.Add(data); return builder.EndVector(); }
  public static void StartCharactersVector(FlatBufferBuilder builder, int numElems) { builder.StartVector(4, numElems, 4); }
  public static Offset<Movie> EndMovie(FlatBufferBuilder builder) {
    int o = builder.EndTable();
    return new Offset<Movie>(o);
  }
  public static void FinishMovieBuffer(FlatBufferBuilder builder, Offset<Movie> offset) { builder.Finish(offset.Value, "MOVI"); }
  public static void FinishSizePrefixedMovieBuffer(FlatBufferBuilder builder, Offset<Movie> offset) { builder.FinishSizePrefixed(offset.Value, "MOVI"); }
};

