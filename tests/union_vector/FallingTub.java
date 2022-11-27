// automatically generated by the FlatBuffers compiler, do not modify

import com.google.flatbuffers.Table;
import com.google.flatbuffers.Struct;
import com.google.flatbuffers.FlatBufferBuilder;
import com.google.flatbuffers.BaseVector;
import com.google.flatbuffers.ByteVector;
import com.google.flatbuffers.UnionVector;
import com.google.flatbuffers.DoubleVector;
import com.google.flatbuffers.StringVector;
import com.google.flatbuffers.BooleanVector;
import com.google.flatbuffers.LongVector;
import com.google.flatbuffers.FloatVector;
import com.google.flatbuffers.Constants;
import java.nio.ByteOrder;
import java.nio.ByteBuffer;

@SuppressWarnings("unused")
public final class FallingTub extends Struct {
  public void __init(int _i, ByteBuffer _bb) { __reset(_i, _bb); }
  public FallingTub __assign(int _i, ByteBuffer _bb) { __init(_i, _bb); return this; }

  public int weight() { return bb.getInt(bb_pos + 0); }
  public void mutateWeight(int weight) { bb.putInt(bb_pos + 0, weight); }

  public static int createFallingTub(FlatBufferBuilder builder, int weight) {
    builder.prep(4, 4);
    builder.putInt(weight);
    return builder.offset();
  }

  public static final class Vector extends BaseVector {
    public Vector __assign(int _vector, int _element_size, ByteBuffer _bb) { __reset(_vector, _element_size, _bb); return this; }

    public FallingTub get(int j) { return get(new FallingTub(), j); }
    public FallingTub get(FallingTub obj, int j) {  return obj.__assign(__element(j), bb); }
  }
  public FallingTubT unpack() {
    FallingTubT _o = new FallingTubT();
    unpackTo(_o);
    return _o;
  }
  public void unpackTo(FallingTubT _o) {
    int _oWeight = weight();
    _o.setWeight(_oWeight);
  }
  public static int pack(FlatBufferBuilder builder, FallingTubT _o) {
    if (_o == null) return 0;
    return createFallingTub(
      builder,
      _o.getWeight());
  }
}

