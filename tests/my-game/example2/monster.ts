// automatically generated by the FlatBuffers compiler, do not modify

import * as flatbuffers from 'flatbuffers';



export class Monster {
  bb: flatbuffers.ByteBuffer|null = null;
  bb_pos = 0;
__init(i:number, bb:flatbuffers.ByteBuffer):Monster {
  this.bb_pos = i;
  this.bb = bb;
  return this;
}

static getRootAsMonster(bb:flatbuffers.ByteBuffer, obj?:Monster):Monster {
  return (obj || new Monster()).__init(bb.readInt32(bb.position()) + bb.position(), bb);
}

static getSizePrefixedRootAsMonster(bb:flatbuffers.ByteBuffer, obj?:Monster):Monster {
  bb.setPosition(bb.position() + flatbuffers.SIZE_PREFIX_LENGTH);
  return (obj || new Monster()).__init(bb.readInt32(bb.position()) + bb.position(), bb);
}

static startMonster(builder:flatbuffers.Builder) {
  builder.startObject(0);
}

static endMonster(builder:flatbuffers.Builder):flatbuffers.Offset {
  const offset = builder.endObject();
  return offset;
}

static createMonster(builder:flatbuffers.Builder):flatbuffers.Offset {
  Monster.startMonster(builder);
  return Monster.endMonster(builder);
}

serialize():Uint8Array {
  return this.bb!.bytes();
}

static deserialize(buffer: Uint8Array):Monster {
  return Monster.getRootAsMonster(new flatbuffers.ByteBuffer(buffer))
}

unpack(): MonsterT {
  return new MonsterT();
}


unpackTo(_o: MonsterT): void {}
}

export class MonsterT {
constructor(){}


pack(builder:flatbuffers.Builder): flatbuffers.Offset {
  return Monster.createMonster(builder);
}
}
