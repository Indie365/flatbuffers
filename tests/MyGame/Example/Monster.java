// automatically generated by the FlatBuffers compiler, do not modify

package MyGame.Example;

import java.nio.*;
import java.lang.*;
import java.util.*;
import com.google.flatbuffers.*;

@SuppressWarnings("unused")
/**
 * an example documentation comment: monster object
 */
public final class Monster extends Table {
  public static Monster getRootAsMonster(ByteBuffer _bb) { return getRootAsMonster(_bb, new Monster()); }
  public static Monster getSizePrefixedRootAsMonster(ByteBuffer _bb) { return getSizePrefixedRootAsMonster(_bb, new Monster()); }
  public static Monster getRootAsMonster(ByteBuffer _bb, Monster obj) { _bb.order(ByteOrder.LITTLE_ENDIAN); return (obj.__assign(_bb.getInt(_bb.position()) + _bb.position(), _bb)); }
  public static Monster getSizePrefixedRootAsMonster(ByteBuffer _bb, Monster obj) { ByteBuffer __bb = _bb.slice(); __bb.position(Constants.SIZE_PREFIX_LENGTH); return getRootAsMonster(__bb, obj); }
  public static int getSizePrefix(ByteBuffer _bb) { _bb.order(ByteOrder.LITTLE_ENDIAN); return _bb.getInt(_bb.position()); }
  public static boolean MonsterBufferHasIdentifier(ByteBuffer _bb) { return __has_identifier(_bb, "MONS"); }
  public void __init(int _i, ByteBuffer _bb) { bb_pos = _i; bb = _bb; }
  public Monster __assign(int _i, ByteBuffer _bb) { __init(_i, _bb); return this; }

  public Vec3 pos() { return pos(new Vec3()); }
  public Vec3 pos(Vec3 obj) { int o = __offset(4); return o != 0 ? obj.__assign(o + bb_pos, bb) : null; }
  public short mana() { int o = __offset(6); return o != 0 ? bb.getShort(o + bb_pos) : 150; }
  public boolean mutateMana(short mana) { int o = __offset(6); if (o != 0) { bb.putShort(o + bb_pos, mana); return true; } else { return false; } }
  public short hp() { int o = __offset(8); return o != 0 ? bb.getShort(o + bb_pos) : 100; }
  public boolean mutateHp(short hp) { int o = __offset(8); if (o != 0) { bb.putShort(o + bb_pos, hp); return true; } else { return false; } }
  public String name() { int o = __offset(10); return o != 0 ? __string(o + bb_pos) : null; }
  public ByteBuffer nameAsByteBuffer() { return __vector_as_bytebuffer(10, 1); }
  public int inventory(int j) { int o = __offset(14); return o != 0 ? bb.get(__vector(o) + j * 1) & 0xFF : 0; }
  public int inventoryLength() { int o = __offset(14); return o != 0 ? __vector_len(o) : 0; }
  public ByteBuffer inventoryAsByteBuffer() { return __vector_as_bytebuffer(14, 1); }
  public boolean mutateInventory(int j, int inventory) { int o = __offset(14); if (o != 0) { bb.put(__vector(o) + j * 1, (byte)inventory); return true; } else { return false; } }
  public byte color() { int o = __offset(16); return o != 0 ? bb.get(o + bb_pos) : 8; }
  public boolean mutateColor(byte color) { int o = __offset(16); if (o != 0) { bb.put(o + bb_pos, color); return true; } else { return false; } }
  public byte testType() { int o = __offset(18); return o != 0 ? bb.get(o + bb_pos) : 0; }
  public boolean mutateTestType(byte test_type) { int o = __offset(18); if (o != 0) { bb.put(o + bb_pos, test_type); return true; } else { return false; } }
  public Table test(Table obj) { int o = __offset(20); return o != 0 ? __union(obj, o) : null; }
  public Test test4(int j) { return test4(new Test(), j); }
  public Test test4(Test obj, int j) { int o = __offset(22); return o != 0 ? obj.__assign(__vector(o) + j * 4, bb) : null; }
  public int test4Length() { int o = __offset(22); return o != 0 ? __vector_len(o) : 0; }
  public String testarrayofstring(int j) { int o = __offset(24); return o != 0 ? __string(__vector(o) + j * 4) : null; }
  public int testarrayofstringLength() { int o = __offset(24); return o != 0 ? __vector_len(o) : 0; }
  /**
   * an example documentation comment: this will end up in the generated code
   * multiline too
   */
  public Monster testarrayoftables(int j) { return testarrayoftables(new Monster(), j); }
  public Monster testarrayoftables(Monster obj, int j) { int o = __offset(26); return o != 0 ? obj.__assign(__indirect(__vector(o) + j * 4), bb) : null; }
  public int testarrayoftablesLength() { int o = __offset(26); return o != 0 ? __vector_len(o) : 0; }
  public Monster testarrayoftablesByKey(String key) { int o = __offset(26); return o != 0 ? Monster.__lookup_by_key(__vector(o), key, bb) : null; }
  public Monster enemy() { return enemy(new Monster()); }
  public Monster enemy(Monster obj) { int o = __offset(28); return o != 0 ? obj.__assign(__indirect(o + bb_pos), bb) : null; }
  public int testnestedflatbuffer(int j) { int o = __offset(30); return o != 0 ? bb.get(__vector(o) + j * 1) & 0xFF : 0; }
  public int testnestedflatbufferLength() { int o = __offset(30); return o != 0 ? __vector_len(o) : 0; }
  public ByteBuffer testnestedflatbufferAsByteBuffer() { return __vector_as_bytebuffer(30, 1); }
  public Monster testnestedflatbufferAsMonster() { return testnestedflatbufferAsMonster(new Monster()); }
  public Monster testnestedflatbufferAsMonster(Monster obj) { int o = __offset(30); return o != 0 ? obj.__assign(__indirect(__vector(o)), bb) : null; }
  public boolean mutateTestnestedflatbuffer(int j, int testnestedflatbuffer) { int o = __offset(30); if (o != 0) { bb.put(__vector(o) + j * 1, (byte)testnestedflatbuffer); return true; } else { return false; } }
  public Stat testempty() { return testempty(new Stat()); }
  public Stat testempty(Stat obj) { int o = __offset(32); return o != 0 ? obj.__assign(__indirect(o + bb_pos), bb) : null; }
  public boolean testbool() { int o = __offset(34); return o != 0 ? 0!=bb.get(o + bb_pos) : false; }
  public boolean mutateTestbool(boolean testbool) { int o = __offset(34); if (o != 0) { bb.put(o + bb_pos, (byte)(testbool ? 1 : 0)); return true; } else { return false; } }
  public int testhashs32Fnv1() { int o = __offset(36); return o != 0 ? bb.getInt(o + bb_pos) : 0; }
  public boolean mutateTesthashs32Fnv1(int testhashs32_fnv1) { int o = __offset(36); if (o != 0) { bb.putInt(o + bb_pos, testhashs32_fnv1); return true; } else { return false; } }
  public long testhashu32Fnv1() { int o = __offset(38); return o != 0 ? (long)bb.getInt(o + bb_pos) & 0xFFFFFFFFL : 0L; }
  public boolean mutateTesthashu32Fnv1(long testhashu32_fnv1) { int o = __offset(38); if (o != 0) { bb.putInt(o + bb_pos, (int)testhashu32_fnv1); return true; } else { return false; } }
  public long testhashs64Fnv1() { int o = __offset(40); return o != 0 ? bb.getLong(o + bb_pos) : 0L; }
  public boolean mutateTesthashs64Fnv1(long testhashs64_fnv1) { int o = __offset(40); if (o != 0) { bb.putLong(o + bb_pos, testhashs64_fnv1); return true; } else { return false; } }
  public long testhashu64Fnv1() { int o = __offset(42); return o != 0 ? bb.getLong(o + bb_pos) : 0L; }
  public boolean mutateTesthashu64Fnv1(long testhashu64_fnv1) { int o = __offset(42); if (o != 0) { bb.putLong(o + bb_pos, testhashu64_fnv1); return true; } else { return false; } }
  public int testhashs32Fnv1a() { int o = __offset(44); return o != 0 ? bb.getInt(o + bb_pos) : 0; }
  public boolean mutateTesthashs32Fnv1a(int testhashs32_fnv1a) { int o = __offset(44); if (o != 0) { bb.putInt(o + bb_pos, testhashs32_fnv1a); return true; } else { return false; } }
  public long testhashu32Fnv1a() { int o = __offset(46); return o != 0 ? (long)bb.getInt(o + bb_pos) & 0xFFFFFFFFL : 0L; }
  public boolean mutateTesthashu32Fnv1a(long testhashu32_fnv1a) { int o = __offset(46); if (o != 0) { bb.putInt(o + bb_pos, (int)testhashu32_fnv1a); return true; } else { return false; } }
  public long testhashs64Fnv1a() { int o = __offset(48); return o != 0 ? bb.getLong(o + bb_pos) : 0L; }
  public boolean mutateTesthashs64Fnv1a(long testhashs64_fnv1a) { int o = __offset(48); if (o != 0) { bb.putLong(o + bb_pos, testhashs64_fnv1a); return true; } else { return false; } }
  public long testhashu64Fnv1a() { int o = __offset(50); return o != 0 ? bb.getLong(o + bb_pos) : 0L; }
  public boolean mutateTesthashu64Fnv1a(long testhashu64_fnv1a) { int o = __offset(50); if (o != 0) { bb.putLong(o + bb_pos, testhashu64_fnv1a); return true; } else { return false; } }
  public boolean testarrayofbools(int j) { int o = __offset(52); return o != 0 ? 0!=bb.get(__vector(o) + j * 1) : false; }
  public int testarrayofboolsLength() { int o = __offset(52); return o != 0 ? __vector_len(o) : 0; }
  public ByteBuffer testarrayofboolsAsByteBuffer() { return __vector_as_bytebuffer(52, 1); }
  public boolean mutateTestarrayofbools(int j, boolean testarrayofbools) { int o = __offset(52); if (o != 0) { bb.put(__vector(o) + j * 1, (byte)(testarrayofbools ? 1 : 0)); return true; } else { return false; } }
  public float testf() { int o = __offset(54); return o != 0 ? bb.getFloat(o + bb_pos) : 3.14159f; }
  public boolean mutateTestf(float testf) { int o = __offset(54); if (o != 0) { bb.putFloat(o + bb_pos, testf); return true; } else { return false; } }
  public float testf2() { int o = __offset(56); return o != 0 ? bb.getFloat(o + bb_pos) : 3.0f; }
  public boolean mutateTestf2(float testf2) { int o = __offset(56); if (o != 0) { bb.putFloat(o + bb_pos, testf2); return true; } else { return false; } }
  public float testf3() { int o = __offset(58); return o != 0 ? bb.getFloat(o + bb_pos) : 0.0f; }
  public boolean mutateTestf3(float testf3) { int o = __offset(58); if (o != 0) { bb.putFloat(o + bb_pos, testf3); return true; } else { return false; } }
  public String testarrayofstring2(int j) { int o = __offset(60); return o != 0 ? __string(__vector(o) + j * 4) : null; }
  public int testarrayofstring2Length() { int o = __offset(60); return o != 0 ? __vector_len(o) : 0; }
  public Ability testarrayofsortedstruct(int j) { return testarrayofsortedstruct(new Ability(), j); }
  public Ability testarrayofsortedstruct(Ability obj, int j) { int o = __offset(62); return o != 0 ? obj.__assign(__vector(o) + j * 8, bb) : null; }
  public int testarrayofsortedstructLength() { int o = __offset(62); return o != 0 ? __vector_len(o) : 0; }
  public int flex(int j) { int o = __offset(64); return o != 0 ? bb.get(__vector(o) + j * 1) & 0xFF : 0; }
  public int flexLength() { int o = __offset(64); return o != 0 ? __vector_len(o) : 0; }
  public ByteBuffer flexAsByteBuffer() { return __vector_as_bytebuffer(64, 1); }
  public boolean mutateFlex(int j, int flex) { int o = __offset(64); if (o != 0) { bb.put(__vector(o) + j * 1, (byte)flex); return true; } else { return false; } }
  public Test test5(int j) { return test5(new Test(), j); }
  public Test test5(Test obj, int j) { int o = __offset(66); return o != 0 ? obj.__assign(__vector(o) + j * 4, bb) : null; }
  public int test5Length() { int o = __offset(66); return o != 0 ? __vector_len(o) : 0; }
  public long vectorOfLongs(int j) { int o = __offset(68); return o != 0 ? bb.getLong(__vector(o) + j * 8) : 0; }
  public int vectorOfLongsLength() { int o = __offset(68); return o != 0 ? __vector_len(o) : 0; }
  public ByteBuffer vectorOfLongsAsByteBuffer() { return __vector_as_bytebuffer(68, 8); }
  public boolean mutateVectorOfLongs(int j, long vector_of_longs) { int o = __offset(68); if (o != 0) { bb.putLong(__vector(o) + j * 8, vector_of_longs); return true; } else { return false; } }
  public double vectorOfDoubles(int j) { int o = __offset(70); return o != 0 ? bb.getDouble(__vector(o) + j * 8) : 0; }
  public int vectorOfDoublesLength() { int o = __offset(70); return o != 0 ? __vector_len(o) : 0; }
  public ByteBuffer vectorOfDoublesAsByteBuffer() { return __vector_as_bytebuffer(70, 8); }
  public boolean mutateVectorOfDoubles(int j, double vector_of_doubles) { int o = __offset(70); if (o != 0) { bb.putDouble(__vector(o) + j * 8, vector_of_doubles); return true; } else { return false; } }
  public MyGame.InParentNamespace parentNamespaceTest() { return parentNamespaceTest(new MyGame.InParentNamespace()); }
  public MyGame.InParentNamespace parentNamespaceTest(MyGame.InParentNamespace obj) { int o = __offset(72); return o != 0 ? obj.__assign(__indirect(o + bb_pos), bb) : null; }

  public static void startMonster(FlatBufferBuilder builder) { builder.startObject(35); }
  public static void addPos(FlatBufferBuilder builder, int posOffset) { builder.addStruct(0, posOffset, 0); }
  public static void addMana(FlatBufferBuilder builder, short mana) { builder.addShort(1, mana, 150); }
  public static void addHp(FlatBufferBuilder builder, short hp) { builder.addShort(2, hp, 100); }
  public static void addName(FlatBufferBuilder builder, int nameOffset) { builder.addOffset(3, nameOffset, 0); }
  public static void addInventory(FlatBufferBuilder builder, int inventoryOffset) { builder.addOffset(5, inventoryOffset, 0); }
  public static int createInventoryVector(FlatBufferBuilder builder, byte[] data) { builder.startVector(1, data.length, 1); for (int i = data.length - 1; i >= 0; i--) builder.addByte(data[i]); return builder.endVector(); }
  public static void startInventoryVector(FlatBufferBuilder builder, int numElems) { builder.startVector(1, numElems, 1); }
  public static void addColor(FlatBufferBuilder builder, byte color) { builder.addByte(6, color, 8); }
  public static void addTestType(FlatBufferBuilder builder, byte testType) { builder.addByte(7, testType, 0); }
  public static void addTest(FlatBufferBuilder builder, int testOffset) { builder.addOffset(8, testOffset, 0); }
  public static void addTest4(FlatBufferBuilder builder, int test4Offset) { builder.addOffset(9, test4Offset, 0); }
  public static void startTest4Vector(FlatBufferBuilder builder, int numElems) { builder.startVector(4, numElems, 2); }
  public static void addTestarrayofstring(FlatBufferBuilder builder, int testarrayofstringOffset) { builder.addOffset(10, testarrayofstringOffset, 0); }
  public static int createTestarrayofstringVector(FlatBufferBuilder builder, int[] data) { builder.startVector(4, data.length, 4); for (int i = data.length - 1; i >= 0; i--) builder.addOffset(data[i]); return builder.endVector(); }
  public static void startTestarrayofstringVector(FlatBufferBuilder builder, int numElems) { builder.startVector(4, numElems, 4); }
  public static void addTestarrayoftables(FlatBufferBuilder builder, int testarrayoftablesOffset) { builder.addOffset(11, testarrayoftablesOffset, 0); }
  public static int createTestarrayoftablesVector(FlatBufferBuilder builder, int[] data) { builder.startVector(4, data.length, 4); for (int i = data.length - 1; i >= 0; i--) builder.addOffset(data[i]); return builder.endVector(); }
  public static void startTestarrayoftablesVector(FlatBufferBuilder builder, int numElems) { builder.startVector(4, numElems, 4); }
  public static void addEnemy(FlatBufferBuilder builder, int enemyOffset) { builder.addOffset(12, enemyOffset, 0); }
  public static void addTestnestedflatbuffer(FlatBufferBuilder builder, int testnestedflatbufferOffset) { builder.addOffset(13, testnestedflatbufferOffset, 0); }
  public static int createTestnestedflatbufferVector(FlatBufferBuilder builder, byte[] data) { builder.startVector(1, data.length, 1); for (int i = data.length - 1; i >= 0; i--) builder.addByte(data[i]); return builder.endVector(); }
  public static void startTestnestedflatbufferVector(FlatBufferBuilder builder, int numElems) { builder.startVector(1, numElems, 1); }
  public static void addTestempty(FlatBufferBuilder builder, int testemptyOffset) { builder.addOffset(14, testemptyOffset, 0); }
  public static void addTestbool(FlatBufferBuilder builder, boolean testbool) { builder.addBoolean(15, testbool, false); }
  public static void addTesthashs32Fnv1(FlatBufferBuilder builder, int testhashs32Fnv1) { builder.addInt(16, testhashs32Fnv1, 0); }
  public static void addTesthashu32Fnv1(FlatBufferBuilder builder, long testhashu32Fnv1) { builder.addInt(17, (int)testhashu32Fnv1, (int)0L); }
  public static void addTesthashs64Fnv1(FlatBufferBuilder builder, long testhashs64Fnv1) { builder.addLong(18, testhashs64Fnv1, 0L); }
  public static void addTesthashu64Fnv1(FlatBufferBuilder builder, long testhashu64Fnv1) { builder.addLong(19, testhashu64Fnv1, 0L); }
  public static void addTesthashs32Fnv1a(FlatBufferBuilder builder, int testhashs32Fnv1a) { builder.addInt(20, testhashs32Fnv1a, 0); }
  public static void addTesthashu32Fnv1a(FlatBufferBuilder builder, long testhashu32Fnv1a) { builder.addInt(21, (int)testhashu32Fnv1a, (int)0L); }
  public static void addTesthashs64Fnv1a(FlatBufferBuilder builder, long testhashs64Fnv1a) { builder.addLong(22, testhashs64Fnv1a, 0L); }
  public static void addTesthashu64Fnv1a(FlatBufferBuilder builder, long testhashu64Fnv1a) { builder.addLong(23, testhashu64Fnv1a, 0L); }
  public static void addTestarrayofbools(FlatBufferBuilder builder, int testarrayofboolsOffset) { builder.addOffset(24, testarrayofboolsOffset, 0); }
  public static int createTestarrayofboolsVector(FlatBufferBuilder builder, boolean[] data) { builder.startVector(1, data.length, 1); for (int i = data.length - 1; i >= 0; i--) builder.addBoolean(data[i]); return builder.endVector(); }
  public static void startTestarrayofboolsVector(FlatBufferBuilder builder, int numElems) { builder.startVector(1, numElems, 1); }
  public static void addTestf(FlatBufferBuilder builder, float testf) { builder.addFloat(25, testf, 3.14159f); }
  public static void addTestf2(FlatBufferBuilder builder, float testf2) { builder.addFloat(26, testf2, 3.0f); }
  public static void addTestf3(FlatBufferBuilder builder, float testf3) { builder.addFloat(27, testf3, 0.0f); }
  public static void addTestarrayofstring2(FlatBufferBuilder builder, int testarrayofstring2Offset) { builder.addOffset(28, testarrayofstring2Offset, 0); }
  public static int createTestarrayofstring2Vector(FlatBufferBuilder builder, int[] data) { builder.startVector(4, data.length, 4); for (int i = data.length - 1; i >= 0; i--) builder.addOffset(data[i]); return builder.endVector(); }
  public static void startTestarrayofstring2Vector(FlatBufferBuilder builder, int numElems) { builder.startVector(4, numElems, 4); }
  public static void addTestarrayofsortedstruct(FlatBufferBuilder builder, int testarrayofsortedstructOffset) { builder.addOffset(29, testarrayofsortedstructOffset, 0); }
  public static void startTestarrayofsortedstructVector(FlatBufferBuilder builder, int numElems) { builder.startVector(8, numElems, 4); }
  public static void addFlex(FlatBufferBuilder builder, int flexOffset) { builder.addOffset(30, flexOffset, 0); }
  public static int createFlexVector(FlatBufferBuilder builder, byte[] data) { builder.startVector(1, data.length, 1); for (int i = data.length - 1; i >= 0; i--) builder.addByte(data[i]); return builder.endVector(); }
  public static void startFlexVector(FlatBufferBuilder builder, int numElems) { builder.startVector(1, numElems, 1); }
  public static void addTest5(FlatBufferBuilder builder, int test5Offset) { builder.addOffset(31, test5Offset, 0); }
  public static void startTest5Vector(FlatBufferBuilder builder, int numElems) { builder.startVector(4, numElems, 2); }
  public static void addVectorOfLongs(FlatBufferBuilder builder, int vectorOfLongsOffset) { builder.addOffset(32, vectorOfLongsOffset, 0); }
  public static int createVectorOfLongsVector(FlatBufferBuilder builder, long[] data) { builder.startVector(8, data.length, 8); for (int i = data.length - 1; i >= 0; i--) builder.addLong(data[i]); return builder.endVector(); }
  public static void startVectorOfLongsVector(FlatBufferBuilder builder, int numElems) { builder.startVector(8, numElems, 8); }
  public static void addVectorOfDoubles(FlatBufferBuilder builder, int vectorOfDoublesOffset) { builder.addOffset(33, vectorOfDoublesOffset, 0); }
  public static int createVectorOfDoublesVector(FlatBufferBuilder builder, double[] data) { builder.startVector(8, data.length, 8); for (int i = data.length - 1; i >= 0; i--) builder.addDouble(data[i]); return builder.endVector(); }
  public static void startVectorOfDoublesVector(FlatBufferBuilder builder, int numElems) { builder.startVector(8, numElems, 8); }
  public static void addParentNamespaceTest(FlatBufferBuilder builder, int parentNamespaceTestOffset) { builder.addOffset(34, parentNamespaceTestOffset, 0); }
  public static int endMonster(FlatBufferBuilder builder) {
    int o = builder.endObject();
    builder.required(o, 10);  // name
    return o;
  }
  public static void finishMonsterBuffer(FlatBufferBuilder builder, int offset) { builder.finish(offset, "MONS"); }
  public static void finishSizePrefixedMonsterBuffer(FlatBufferBuilder builder, int offset) { builder.finishSizePrefixed(offset, "MONS"); }

  @Override
  protected int keysCompare(Integer o1, Integer o2, ByteBuffer _bb) { return compareStrings(__offset(10, o1, _bb), __offset(10, o2, _bb), _bb); }

  public static Monster __lookup_by_key(int vectorLocation, String key, ByteBuffer bb) {
    byte[] byteKey = key.getBytes(Table.UTF8_CHARSET.get());
    int span = bb.getInt(vectorLocation - 4);
    int start = 0;
    while (span != 0) {
      int middle = span / 2;
      int tableOffset = __indirect(vectorLocation + 4 * (start + middle), bb);
      int comp = compareStrings(__offset(10, bb.capacity() - tableOffset, bb), byteKey, bb);
      if (comp > 0) {
        span = middle;
      } else if (comp < 0) {
        middle++;
        start += middle;
        span -= middle;
      } else {
        return new Monster().__assign(tableOffset, bb);
      }
    }
    return null;
  }
}

