// automatically generated by the FlatBuffers compiler, do not modify
import { Ability } from '../../my-game/example/ability.js';
import { Test } from '../../my-game/example/test.js';
export class StructOfStructs {
    constructor() {
        this.bb = null;
        this.bb_pos = 0;
    }
    __init(i, bb) {
        this.bb_pos = i;
        this.bb = bb;
        return this;
    }
    a(obj) {
        return (obj || new Ability()).__init(this.bb_pos, this.bb);
    }
    b(obj) {
        return (obj || new Test()).__init(this.bb_pos + 8, this.bb);
    }
    c(obj) {
        return (obj || new Ability()).__init(this.bb_pos + 12, this.bb);
    }
    static getFullyQualifiedName() {
        return 'MyGame_Example_StructOfStructs';
    }
    static sizeOf() {
        return 20;
    }
    static createStructOfStructs(builder, a_id, a_distance, b_a, b_b, c_id, c_distance) {
        builder.prep(4, 20);
        builder.prep(4, 8);
        builder.writeInt32(c_distance);
        builder.writeInt32(c_id);
        builder.prep(2, 4);
        builder.pad(1);
        builder.writeInt8(b_b);
        builder.writeInt16(b_a);
        builder.prep(4, 8);
        builder.writeInt32(a_distance);
        builder.writeInt32(a_id);
        return builder.offset();
    }
    unpack() {
        return new StructOfStructsT((this.a() !== null ? this.a().unpack() : null), (this.b() !== null ? this.b().unpack() : null), (this.c() !== null ? this.c().unpack() : null));
    }
    unpackTo(_o) {
        _o.a = (this.a() !== null ? this.a().unpack() : null);
        _o.b = (this.b() !== null ? this.b().unpack() : null);
        _o.c = (this.c() !== null ? this.c().unpack() : null);
    }
}
export class StructOfStructsT {
    constructor(a = null, b = null, c = null) {
        this.a = a;
        this.b = b;
        this.c = c;
    }
    pack(builder) {
        return StructOfStructs.createStructOfStructs(builder, (this.a?.id ?? 0), (this.a?.distance ?? 0), (this.b?.a ?? 0), (this.b?.b ?? 0), (this.c?.id ?? 0), (this.c?.distance ?? 0));
    }
}
