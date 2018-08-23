// automatically generated by the FlatBuffers compiler, do not modify

import * as NS9459827973991502386 from "./namespace_test1_generated";
/**
 * @constructor
 */
export namespace NamespaceA{
export class TableInFirstNS {
  bb: flatbuffers.ByteBuffer|null = null;

  bb_pos:number = 0;
/**
 * @param number i
 * @param flatbuffers.ByteBuffer bb
 * @returns TableInFirstNS
 */
__init(i:number, bb:flatbuffers.ByteBuffer):TableInFirstNS {
  this.bb_pos = i;
  this.bb = bb;
  return this;
};

/**
 * @param flatbuffers.ByteBuffer bb
 * @param TableInFirstNS= obj
 * @returns TableInFirstNS
 */
static getRootAsTableInFirstNS(bb:flatbuffers.ByteBuffer, obj?:TableInFirstNS):TableInFirstNS {
  return (obj || new TableInFirstNS).__init(bb.readInt32(bb.position()) + bb.position(), bb);
};

/**
 * @param NamespaceA.NamespaceB.TableInNestedNS= obj
 * @returns NamespaceA.NamespaceB.TableInNestedNS|null
 */
fooTable(obj?:NS9459827973991502386.NamespaceA.NamespaceB.TableInNestedNS):NS9459827973991502386.NamespaceA.NamespaceB.TableInNestedNS|null {
  var offset = this.bb!.__offset(this.bb_pos, 4);
  return offset ? (obj || new NS9459827973991502386.NamespaceA.NamespaceB.TableInNestedNS).__init(this.bb!.__indirect(this.bb_pos + offset), this.bb!) : null;
};

/**
 * @returns NamespaceA.NamespaceB.EnumInNestedNS
 */
fooEnum():NS9459827973991502386.NamespaceA.NamespaceB.EnumInNestedNS {
  var offset = this.bb!.__offset(this.bb_pos, 6);
  return offset ? /** @type {NamespaceA.NamespaceB.EnumInNestedNS} */ (this.bb!.readInt8(this.bb_pos + offset)) : NS9459827973991502386.NamespaceA.NamespaceB.EnumInNestedNS.A;
};

/**
 * @param NamespaceA.NamespaceB.EnumInNestedNS value
 * @returns boolean
 */
mutate_foo_enum(value:NS9459827973991502386.NamespaceA.NamespaceB.EnumInNestedNS):boolean {
  var offset = this.bb!.__offset(this.bb_pos, 6);

  if (offset === 0) {
    return false;
  }

  this.bb!.writeInt8(this.bb_pos + offset, value);
  return true;
};

/**
 * @param NamespaceA.NamespaceB.StructInNestedNS= obj
 * @returns NamespaceA.NamespaceB.StructInNestedNS|null
 */
fooStruct(obj?:NS9459827973991502386.NamespaceA.NamespaceB.StructInNestedNS):NS9459827973991502386.NamespaceA.NamespaceB.StructInNestedNS|null {
  var offset = this.bb!.__offset(this.bb_pos, 8);
  return offset ? (obj || new NS9459827973991502386.NamespaceA.NamespaceB.StructInNestedNS).__init(this.bb_pos + offset, this.bb!) : null;
};

/**
 * @param flatbuffers.Builder builder
 */
static startTableInFirstNS(builder:flatbuffers.Builder) {
  builder.startObject(3);
};

/**
 * @param flatbuffers.Builder builder
 * @param flatbuffers.Offset fooTableOffset
 */
static addFooTable(builder:flatbuffers.Builder, fooTableOffset:flatbuffers.Offset) {
  builder.addFieldOffset(0, fooTableOffset, 0);
};

/**
 * @param flatbuffers.Builder builder
 * @param NamespaceA.NamespaceB.EnumInNestedNS fooEnum
 */
static addFooEnum(builder:flatbuffers.Builder, fooEnum:NS9459827973991502386.NamespaceA.NamespaceB.EnumInNestedNS) {
  builder.addFieldInt8(1, fooEnum, NS9459827973991502386.NamespaceA.NamespaceB.EnumInNestedNS.A);
};

/**
 * @param flatbuffers.Builder builder
 * @param flatbuffers.Offset fooStructOffset
 */
static addFooStruct(builder:flatbuffers.Builder, fooStructOffset:flatbuffers.Offset) {
  builder.addFieldStruct(2, fooStructOffset, 0);
};

/**
 * @param flatbuffers.Builder builder
 * @returns flatbuffers.Offset
 */
static endTableInFirstNS(builder:flatbuffers.Builder):flatbuffers.Offset {
  var offset = builder.endObject();
  return offset;
};

}
}
/**
 * @constructor
 */
export namespace NamespaceC{
export class TableInC {
  bb: flatbuffers.ByteBuffer|null = null;

  bb_pos:number = 0;
/**
 * @param number i
 * @param flatbuffers.ByteBuffer bb
 * @returns TableInC
 */
__init(i:number, bb:flatbuffers.ByteBuffer):TableInC {
  this.bb_pos = i;
  this.bb = bb;
  return this;
};

/**
 * @param flatbuffers.ByteBuffer bb
 * @param TableInC= obj
 * @returns TableInC
 */
static getRootAsTableInC(bb:flatbuffers.ByteBuffer, obj?:TableInC):TableInC {
  return (obj || new TableInC).__init(bb.readInt32(bb.position()) + bb.position(), bb);
};

/**
 * @param NamespaceA.TableInFirstNS= obj
 * @returns NamespaceA.TableInFirstNS|null
 */
referToA1(obj?:NamespaceA.TableInFirstNS):NamespaceA.TableInFirstNS|null {
  var offset = this.bb!.__offset(this.bb_pos, 4);
  return offset ? (obj || new NamespaceA.TableInFirstNS).__init(this.bb!.__indirect(this.bb_pos + offset), this.bb!) : null;
};

/**
 * @param NamespaceA.SecondTableInA= obj
 * @returns NamespaceA.SecondTableInA|null
 */
referToA2(obj?:NamespaceA.SecondTableInA):NamespaceA.SecondTableInA|null {
  var offset = this.bb!.__offset(this.bb_pos, 6);
  return offset ? (obj || new NamespaceA.SecondTableInA).__init(this.bb!.__indirect(this.bb_pos + offset), this.bb!) : null;
};

/**
 * @param flatbuffers.Builder builder
 */
static startTableInC(builder:flatbuffers.Builder) {
  builder.startObject(2);
};

/**
 * @param flatbuffers.Builder builder
 * @param flatbuffers.Offset referToA1Offset
 */
static addReferToA1(builder:flatbuffers.Builder, referToA1Offset:flatbuffers.Offset) {
  builder.addFieldOffset(0, referToA1Offset, 0);
};

/**
 * @param flatbuffers.Builder builder
 * @param flatbuffers.Offset referToA2Offset
 */
static addReferToA2(builder:flatbuffers.Builder, referToA2Offset:flatbuffers.Offset) {
  builder.addFieldOffset(1, referToA2Offset, 0);
};

/**
 * @param flatbuffers.Builder builder
 * @returns flatbuffers.Offset
 */
static endTableInC(builder:flatbuffers.Builder):flatbuffers.Offset {
  var offset = builder.endObject();
  return offset;
};

}
}
/**
 * @constructor
 */
export namespace NamespaceA{
export class SecondTableInA {
  bb: flatbuffers.ByteBuffer|null = null;

  bb_pos:number = 0;
/**
 * @param number i
 * @param flatbuffers.ByteBuffer bb
 * @returns SecondTableInA
 */
__init(i:number, bb:flatbuffers.ByteBuffer):SecondTableInA {
  this.bb_pos = i;
  this.bb = bb;
  return this;
};

/**
 * @param flatbuffers.ByteBuffer bb
 * @param SecondTableInA= obj
 * @returns SecondTableInA
 */
static getRootAsSecondTableInA(bb:flatbuffers.ByteBuffer, obj?:SecondTableInA):SecondTableInA {
  return (obj || new SecondTableInA).__init(bb.readInt32(bb.position()) + bb.position(), bb);
};

/**
 * @param NamespaceC.TableInC= obj
 * @returns NamespaceC.TableInC|null
 */
referToC(obj?:NamespaceC.TableInC):NamespaceC.TableInC|null {
  var offset = this.bb!.__offset(this.bb_pos, 4);
  return offset ? (obj || new NamespaceC.TableInC).__init(this.bb!.__indirect(this.bb_pos + offset), this.bb!) : null;
};

/**
 * @param flatbuffers.Builder builder
 */
static startSecondTableInA(builder:flatbuffers.Builder) {
  builder.startObject(1);
};

/**
 * @param flatbuffers.Builder builder
 * @param flatbuffers.Offset referToCOffset
 */
static addReferToC(builder:flatbuffers.Builder, referToCOffset:flatbuffers.Offset) {
  builder.addFieldOffset(0, referToCOffset, 0);
};

/**
 * @param flatbuffers.Builder builder
 * @returns flatbuffers.Offset
 */
static endSecondTableInA(builder:flatbuffers.Builder):flatbuffers.Offset {
  var offset = builder.endObject();
  return offset;
};

}
}
