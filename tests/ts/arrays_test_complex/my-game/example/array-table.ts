// automatically generated by the FlatBuffers compiler, do not modify

import * as flatbuffers from 'flatbuffers';

import { ArrayStruct, ArrayStructT } from '../../my-game/example/array-struct.js';


export class ArrayTable implements flatbuffers.IUnpackableObject<ArrayTableT> {
  bb: flatbuffers.ByteBuffer|null = null;
  bb_pos = 0;
  __init(i:number, bb:flatbuffers.ByteBuffer):ArrayTable {
  this.bb_pos = i;
  this.bb = bb;
  return this;
}

static getRootAsArrayTable(bb:flatbuffers.ByteBuffer, obj?:ArrayTable):ArrayTable {
  return (obj || new ArrayTable()).__init(bb.readInt32(bb.position()) + bb.position(), bb);
}

static getSizePrefixedRootAsArrayTable(bb:flatbuffers.ByteBuffer, obj?:ArrayTable):ArrayTable {
  bb.setPosition(bb.position() + flatbuffers.SIZE_PREFIX_LENGTH);
  return (obj || new ArrayTable()).__init(bb.readInt32(bb.position()) + bb.position(), bb);
}

static bufferHasIdentifier(bb:flatbuffers.ByteBuffer):boolean {
  return bb.__has_identifier('RHUB');
}

a():string|null
a(optionalEncoding:flatbuffers.Encoding):string|Uint8Array|null
a(optionalEncoding?:any):string|Uint8Array|null {
  const offset = this.bb!.__offset(this.bb_pos, 4);
  return offset ? this.bb!.__string(this.bb_pos + offset, optionalEncoding) : null;
}

cUnderscore(obj?:ArrayStruct):ArrayStruct|null {
  const offset = this.bb!.__offset(this.bb_pos, 6);
  return offset ? (obj || new ArrayStruct()).__init(this.bb_pos + offset, this.bb!) : null;
}

static getFullyQualifiedName():string {
  return 'MyGame_Example_ArrayTable';
}

static startArrayTable(builder:flatbuffers.Builder) {
  builder.startObject(2);
}

static addA(builder:flatbuffers.Builder, aOffset:flatbuffers.Offset) {
  builder.addFieldOffset(0, aOffset, 0);
}

static addCUnderscore(builder:flatbuffers.Builder, cUnderscoreOffset:flatbuffers.Offset) {
  builder.addFieldStruct(1, cUnderscoreOffset, 0);
}

static endArrayTable(builder:flatbuffers.Builder):flatbuffers.Offset {
  const offset = builder.endObject();
  return offset;
}

static finishArrayTableBuffer(builder:flatbuffers.Builder, offset:flatbuffers.Offset) {
  builder.finish(offset, 'RHUB');
}

static finishSizePrefixedArrayTableBuffer(builder:flatbuffers.Builder, offset:flatbuffers.Offset) {
  builder.finish(offset, 'RHUB', true);
}


unpack(): ArrayTableT {
  return new ArrayTableT(
    this.a(),
    (this.cUnderscore() !== null ? this.cUnderscore()!.unpack() : null)
  );
}


unpackTo(_o: ArrayTableT): void {
  _o.a = this.a();
  _o.cUnderscore = (this.cUnderscore() !== null ? this.cUnderscore()!.unpack() : null);
}
}

export class ArrayTableT implements flatbuffers.IGeneratedObject {
constructor(
  public a: string|Uint8Array|null = null,
  public cUnderscore: ArrayStructT|null = null
){}


pack(builder:flatbuffers.Builder): flatbuffers.Offset {
  const a = (this.a !== null ? builder.createString(this.a!) : 0);

  ArrayTable.startArrayTable(builder);
  ArrayTable.addA(builder, a);
  ArrayTable.addCUnderscore(builder, (this.cUnderscore !== null ? this.cUnderscore!.pack(builder) : 0));

  return ArrayTable.endArrayTable(builder);
}
}
