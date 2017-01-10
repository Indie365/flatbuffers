// automatically generated by the FlatBuffers compiler, do not modify

package Testing.KeySearch;

import java.nio.*;
import java.lang.*;
import java.util.*;
import com.google.flatbuffers.*;

@SuppressWarnings("unused")
public final class UShortEntry extends Table {
  public static UShortEntry getRootAsUShortEntry(ByteBuffer _bb) { return getRootAsUShortEntry(_bb, new UShortEntry()); }
  public static UShortEntry getRootAsUShortEntry(ByteBuffer _bb, UShortEntry obj) { _bb.order(ByteOrder.LITTLE_ENDIAN); return (obj.__assign(_bb.getInt(_bb.position()) + _bb.position(), _bb)); }
  public UShortEntry __assign(int _i, ByteBuffer _bb) { __init(_i, _bb); return this; }

  public int key() { int o = __offset(4); return o != 0 ? bb.getShort(o + bb_pos) & 0xFFFF : 0; }
  public boolean mutateKey(int key) { int o = __offset(4); if (o != 0) { bb.putShort(o + bb_pos, (short)key); return true; } else { return false; } }
  public int value() { int o = __offset(6); return o != 0 ? bb.getShort(o + bb_pos) & 0xFFFF : 65535; }
  public boolean mutateValue(int value) { int o = __offset(6); if (o != 0) { bb.putShort(o + bb_pos, (short)value); return true; } else { return false; } }

  public static int createUShortEntry(FlatBufferBuilder builder,
      int key,
      int value) {
    builder.startObject(2);
    UShortEntry.addValue(builder, value);
    UShortEntry.addKey(builder, key);
    return UShortEntry.endUShortEntry(builder);
  }

  public static void startUShortEntry(FlatBufferBuilder builder) { builder.startObject(2); }
  public static void addKey(FlatBufferBuilder builder, int key) { builder.addShort(0, (short)key, (short)0); }
  public static void addValue(FlatBufferBuilder builder, int value) { builder.addShort(1, (short)value, (short)65535); }
  public static int endUShortEntry(FlatBufferBuilder builder) {
    int o = builder.endObject();
    return o;
  }

  @Override
  protected int keysCompare(Integer o1, Integer o2, ByteBuffer _bb) {
    short val_1 = _bb.getShort(o1+__offset(4, o1, _bb));
    short val_2 = _bb.getShort(o2+__offset(4, o2, _bb));
    return val_1 > val_2 ? 1 : val_1 < val_2 ? -1 : 0;
  }

  public static int lookupByKey( int bb_pos, int fieldDataOffset, int key, int defaultKeyValue , ByteBuffer bb) {
    if ( fieldDataOffset == 0 )
        return 0;
    int vectorOffsetPos = bb_pos + fieldDataOffset;
    int vectorLocation = bb.getInt( vectorOffsetPos ) + vectorOffsetPos;
    int span = bb.getInt(vectorLocation);
    vectorLocation += 4;
    int comparableKey = Unsigneds.asComparable( (short) key );
    int comparableDefault = Unsigneds.asComparable( (short)defaultKeyValue );
    int start = 0;
    while (span != 0) {
      int middle = span / 2;
      int tableOffset = __indirect(vectorLocation + 4 * (start + middle), bb);
      int keyValueOffset = __offset( 4, tableOffset, bb );
      int val = keyValueOffset != 0 ? Unsigneds.asComparable( bb.getShort(tableOffset + keyValueOffset) ): comparableDefault;
      if (comparableKey < val) {
        span = middle;
      } else if (comparableKey > val) {
        middle++;
        start += middle;
        span -= middle;
      } else {
        return tableOffset;
      }
    }
    return 0;
  }
}

