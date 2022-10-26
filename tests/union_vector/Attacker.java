// automatically generated by the FlatBuffers compiler, do not modify

import java.nio.*;
import java.lang.*;
import java.util.*;
import com.google.flatbuffers.*;

@SuppressWarnings("unused")
public final class Attacker extends Table {
  public static void ValidateVersion() { Constants.FLATBUFFERS_22_10_25(); }
  public static Attacker getRootAsAttacker(ByteBuffer _bb) { return getRootAsAttacker(_bb, new Attacker()); }
  public static Attacker getRootAsAttacker(ByteBuffer _bb, Attacker obj) { _bb.order(ByteOrder.LITTLE_ENDIAN); return (obj.__assign(_bb.getInt(_bb.position()) + _bb.position(), _bb)); }
  public void __init(int _i, ByteBuffer _bb) { __reset(_i, _bb); }
  public Attacker __assign(int _i, ByteBuffer _bb) { __init(_i, _bb); return this; }

  public int swordAttackDamage() { int o = __offset(4); return o != 0 ? bb.getInt(o + bb_pos) : 0; }
  public boolean mutateSwordAttackDamage(int sword_attack_damage) { int o = __offset(4); if (o != 0) { bb.putInt(o + bb_pos, sword_attack_damage); return true; } else { return false; } }

  public static int createAttacker(FlatBufferBuilder builder,
      int swordAttackDamage) {
    builder.startTable(1);
    Attacker.addSwordAttackDamage(builder, swordAttackDamage);
    return Attacker.endAttacker(builder);
  }

  public static void startAttacker(FlatBufferBuilder builder) { builder.startTable(1); }
  public static void addSwordAttackDamage(FlatBufferBuilder builder, int swordAttackDamage) { builder.addInt(0, swordAttackDamage, 0); }
  public static int endAttacker(FlatBufferBuilder builder) {
    int o = builder.endTable();
    return o;
  }

  public static final class Vector extends BaseVector {
    public Vector __assign(int _vector, int _element_size, ByteBuffer _bb) { __reset(_vector, _element_size, _bb); return this; }

    public Attacker get(int j) { return get(new Attacker(), j); }
    public Attacker get(Attacker obj, int j) {  return obj.__assign(__indirect(__element(j), bb), bb); }
  }
  public AttackerT unpack() {
    AttackerT _o = new AttackerT();
    unpackTo(_o);
    return _o;
  }
  public void unpackTo(AttackerT _o) {
    int _oSwordAttackDamage = swordAttackDamage();
    _o.setSwordAttackDamage(_oSwordAttackDamage);
  }
  public static int pack(FlatBufferBuilder builder, AttackerT _o) {
    if (_o == null) return 0;
    return createAttacker(
      builder,
      _o.getSwordAttackDamage());
  }
}

