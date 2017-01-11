// automatically generated by the FlatBuffers compiler, do not modify

package MyGame.Example;

import java.nio.*;
import java.lang.*;
import java.util.*;
import com.google.flatbuffers.*;

@SuppressWarnings("unused")
public final class Stat extends Table {
  public static Stat getRootAsStat(ByteBuffer _bb) { return getRootAsStat(_bb, new Stat()); }
  public static Stat getRootAsStat(ByteBuffer _bb, Stat obj) { _bb.order(ByteOrder.LITTLE_ENDIAN); return (obj.__assign(_bb.getInt(_bb.position()) + _bb.position(), _bb)); }
  public Stat __assign(int _i, ByteBuffer _bb) { __init(_i, _bb); return this; }

  public String id() { int o = __offset(4); return o != 0 ? __string(o + bb_pos) : null; }
  public ByteBuffer idAsByteBuffer() { return __vector_as_bytebuffer(4, 1); }
  public long val() { int o = __offset(6); return o != 0 ? bb.getLong(o + bb_pos) : 0L; }
  public boolean mutateVal(long val) { int o = __offset(6); if (o != 0) { bb.putLong(o + bb_pos, val); return true; } else { return false; } }
  public int count() { int o = __offset(8); return o != 0 ? bb.getShort(o + bb_pos) & 0xFFFF : 0; }
  public boolean mutateCount(int count) { int o = __offset(8); if (o != 0) { bb.putShort(o + bb_pos, (short)count); return true; } else { return false; } }

  public static int createStat(FlatBufferBuilder builder,
      int idOffset,
      long val,
      int count) {
    builder.startObject(3);
    Stat.addVal(builder, val);
    Stat.addId(builder, idOffset);
    Stat.addCount(builder, count);
    return Stat.endStat(builder);
  }

  public static void startStat(FlatBufferBuilder builder) { builder.startObject(3); }
  public static void addId(FlatBufferBuilder builder, int idOffset) { builder.addOffset(0, idOffset, 0); }
  public static void addVal(FlatBufferBuilder builder, long val) { builder.addLong(1, val, 0L); }
  public static void addCount(FlatBufferBuilder builder, int count) { builder.addShort(2, (short)count, (short)0); }
  public static int endStat(FlatBufferBuilder builder) {
    int o = builder.endObject();
    return o;
  }
}

