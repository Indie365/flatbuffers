// automatically generated by the FlatBuffers compiler, do not modify

package MyGame.Example;

import java.nio.*;
import java.lang.*;
import java.util.*;
import com.google.flatbuffers.*;

@SuppressWarnings("unused")
public final class StringKey extends Table {
  public static void ValidateVersion() { Constants.FLATBUFFERS_1_12_0(); }
  public static StringKey getRootAsStringKey(ByteBuffer _bb) { return getRootAsStringKey(_bb, new StringKey()); }
  public static StringKey getRootAsStringKey(ByteBuffer _bb, StringKey obj) { _bb.order(ByteOrder.LITTLE_ENDIAN); return (obj.__assign(_bb.getInt(_bb.position()) + _bb.position(), _bb)); }
  public void __init(int _i, ByteBuffer _bb) { __reset(_i, _bb); }
  public StringKey __assign(int _i, ByteBuffer _bb) { __init(_i, _bb); return this; }

  public String k() { int o = __offset(4); return o != 0 ? __string(o + bb_pos) : null; }
  public ByteBuffer kAsByteBuffer() { return __vector_as_bytebuffer(4, 1); }
  public ByteBuffer kInByteBuffer(ByteBuffer _bb) { return __vector_in_bytebuffer(_bb, 4, 1); }

  public static int createStringKey(FlatBufferBuilder builder,
      int kOffset) {
    builder.startTable(1);
    StringKey.addK(builder, kOffset);
    return StringKey.endStringKey(builder);
  }

  public static void startStringKey(FlatBufferBuilder builder) { builder.startTable(1); }
  public static void addK(FlatBufferBuilder builder, int kOffset) { builder.addOffset(0, kOffset, 0); }
  public static int endStringKey(FlatBufferBuilder builder) {
    int o = builder.endTable();
    builder.required(o, 4);  // k
    return o;
  }

  @Override
  protected int keysCompare(Integer o1, Integer o2, ByteBuffer _bb) { return compareStrings(__offset(4, o1, _bb), __offset(4, o2, _bb), _bb); }

  public static StringKey __lookup_by_key(StringKey obj, int vectorLocation, String key, ByteBuffer bb) {
    byte[] byteKey = key.getBytes(java.nio.charset.StandardCharsets.UTF_8);
    int span = bb.getInt(vectorLocation - 4);
    int start = 0;
    while (span != 0) {
      int middle = span / 2;
      int tableOffset = __indirect(vectorLocation + 4 * (start + middle), bb);
      int comp = compareStrings(__offset(4, bb.capacity() - tableOffset, bb), byteKey, bb);
      if (comp > 0) {
        span = middle;
      } else if (comp < 0) {
        middle++;
        start += middle;
        span -= middle;
      } else {
        return (obj == null ? new StringKey() : obj).__assign(tableOffset, bb);
      }
    }
    return null;
  }

  public static final class Vector extends BaseVector {
    public Vector __assign(int _vector, int _element_size, ByteBuffer _bb) { __reset(_vector, _element_size, _bb); return this; }

    public StringKey get(int j) { return get(new StringKey(), j); }
    public StringKey get(StringKey obj, int j) {  return obj.__assign(__indirect(__element(j), bb), bb); }
    public StringKey getByKey(String key) {  return __lookup_by_key(null, __vector(), key, bb); }
    public StringKey getByKey(StringKey obj, String key) {  return __lookup_by_key(obj, __vector(), key, bb); }
  }
}

