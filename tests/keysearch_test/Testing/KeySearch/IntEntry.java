// automatically generated by the FlatBuffers compiler, do not modify

package Testing.KeySearch;

import java.nio.*;
import java.lang.*;
import java.util.*;
import com.google.flatbuffers.*;

@SuppressWarnings("unused")
public final class IntEntry extends Table {
  public static IntEntry getRootAsIntEntry(ByteBuffer _bb) { return getRootAsIntEntry(_bb, new IntEntry()); }
  public static IntEntry getRootAsIntEntry(ByteBuffer _bb, IntEntry obj) { _bb.order(ByteOrder.LITTLE_ENDIAN); return (obj.__assign(_bb.getInt(_bb.position()) + _bb.position(), _bb)); }
  public IntEntry __assign(int _i, ByteBuffer _bb) { __init(_i, _bb); return this; }

  public int key() { int o = __offset(4); return o != 0 ? bb.getInt(o + bb_pos) : -2147483648; }
  public boolean mutateKey(int key) { int o = __offset(4); if (o != 0) { bb.putInt(o + bb_pos, key); return true; } else { return false; } }
  public int value() { int o = __offset(6); return o != 0 ? bb.getInt(o + bb_pos) : -2147483648; }
  public boolean mutateValue(int value) { int o = __offset(6); if (o != 0) { bb.putInt(o + bb_pos, value); return true; } else { return false; } }

  public static int createIntEntry(FlatBufferBuilder builder,
      int key,
      int value) {
    builder.startObject(2);
    IntEntry.addValue(builder, value);
    IntEntry.addKey(builder, key);
    return IntEntry.endIntEntry(builder);
  }

  public static void startIntEntry(FlatBufferBuilder builder) { builder.startObject(2); }
  public static void addKey(FlatBufferBuilder builder, int key) { builder.addInt(0, key, -2147483648); }
  public static void addValue(FlatBufferBuilder builder, int value) { builder.addInt(1, value, -2147483648); }
  public static int endIntEntry(FlatBufferBuilder builder) {
    int o = builder.endObject();
    return o;
  }

  @Override
  protected int keysCompare(Integer o1, Integer o2, ByteBuffer _bb) {
    int val_1 = _bb.getInt(o1+__offset(4, o1, _bb));
    int val_2 = _bb.getInt(o2+__offset(4, o2, _bb));
    return val_1 > val_2 ? 1 : val_1 < val_2 ? -1 : 0;
  }

  public static int lookupByKey( int bb_pos, int fieldDataOffset, int key, int defaultKeyValue , ByteBuffer bb) {
    if ( fieldDataOffset == 0 )
        return 0;
    int vectorOffsetPos = bb_pos + fieldDataOffset;
    int vectorLocation = bb.getInt( vectorOffsetPos ) + vectorOffsetPos;
    int span = bb.getInt(vectorLocation);
    vectorLocation += 4;
    int start = 0;
    while (span != 0) {
      int middle = span / 2;
      int tableOffset = __indirect(vectorLocation + 4 * (start + middle), bb);
      int keyValueOffset = __offset( 4, tableOffset, bb );
      int val = keyValueOffset != 0 ? bb.getInt(tableOffset + keyValueOffset) : defaultKeyValue;
      if (key < val) {
        span = middle;
      } else if (key > val) {
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

