// automatically generated by the FlatBuffers compiler, do not modify
/* eslint-disable @typescript-eslint/no-unused-vars, @typescript-eslint/no-explicit-any, @typescript-eslint/no-non-null-assertion */
import * as flatbuffers from 'flatbuffers';
import { Abc } from '../foobar/abc.js';
import { class_ as foobar_class_ } from '../foobar/class.js';
import { Schema } from '../reflection/schema.js';
import { class_ } from '../typescript/class.js';
export class Object_ {
    constructor() {
        this.bb = null;
        this.bb_pos = 0;
    }
    __init(i, bb) {
        this.bb_pos = i;
        this.bb = bb;
        return this;
    }
    static getRootAsObject(bb, obj) {
        return (obj || new Object_()).__init(bb.readInt32(bb.position()) + bb.position(), bb);
    }
    static getSizePrefixedRootAsObject(bb, obj) {
        bb.setPosition(bb.position() + flatbuffers.SIZE_PREFIX_LENGTH);
        return (obj || new Object_()).__init(bb.readInt32(bb.position()) + bb.position(), bb);
    }
    return_() {
        const offset = this.bb.__offset(this.bb_pos, 4);
        return offset ? this.bb.readInt32(this.bb_pos + offset) : 0;
    }
    mutate_return(value) {
        const offset = this.bb.__offset(this.bb_pos, 4);
        if (offset === 0) {
            return false;
        }
        this.bb.writeInt32(this.bb_pos + offset, value);
        return true;
    }
    if_() {
        const offset = this.bb.__offset(this.bb_pos, 6);
        return offset ? this.bb.readInt32(this.bb_pos + offset) : 0;
    }
    mutate_if(value) {
        const offset = this.bb.__offset(this.bb_pos, 6);
        if (offset === 0) {
            return false;
        }
        this.bb.writeInt32(this.bb_pos + offset, value);
        return true;
    }
    switch_() {
        const offset = this.bb.__offset(this.bb_pos, 8);
        return offset ? this.bb.readInt32(this.bb_pos + offset) : 0;
    }
    mutate_switch(value) {
        const offset = this.bb.__offset(this.bb_pos, 8);
        if (offset === 0) {
            return false;
        }
        this.bb.writeInt32(this.bb_pos + offset, value);
        return true;
    }
    enum_() {
        const offset = this.bb.__offset(this.bb_pos, 10);
        return offset ? this.bb.readInt32(this.bb_pos + offset) : class_.new_;
    }
    mutate_enum(value) {
        const offset = this.bb.__offset(this.bb_pos, 10);
        if (offset === 0) {
            return false;
        }
        this.bb.writeInt32(this.bb_pos + offset, value);
        return true;
    }
    enum2() {
        const offset = this.bb.__offset(this.bb_pos, 12);
        return offset ? this.bb.readInt32(this.bb_pos + offset) : foobar_class_.arguments_;
    }
    mutate_enum2(value) {
        const offset = this.bb.__offset(this.bb_pos, 12);
        if (offset === 0) {
            return false;
        }
        this.bb.writeInt32(this.bb_pos + offset, value);
        return true;
    }
    enum3() {
        const offset = this.bb.__offset(this.bb_pos, 14);
        return offset ? this.bb.readInt32(this.bb_pos + offset) : Abc.a;
    }
    mutate_enum3(value) {
        const offset = this.bb.__offset(this.bb_pos, 14);
        if (offset === 0) {
            return false;
        }
        this.bb.writeInt32(this.bb_pos + offset, value);
        return true;
    }
    reflect(obj) {
        const offset = this.bb.__offset(this.bb_pos, 16);
        return offset ? (obj || new Schema()).__init(this.bb.__indirect(this.bb_pos + offset), this.bb) : null;
    }
    static getFullyQualifiedName() {
        return 'typescript.Object';
    }
    static startObject(builder) {
        builder.startObject(7);
    }
    static addReturn(builder, return_) {
        builder.addFieldInt32(0, return_, 0);
    }
    static addIf(builder, if_) {
        builder.addFieldInt32(1, if_, 0);
    }
    static addSwitch(builder, switch_) {
        builder.addFieldInt32(2, switch_, 0);
    }
    static addEnum(builder, enum_) {
        builder.addFieldInt32(3, enum_, class_.new_);
    }
    static addEnum2(builder, enum2) {
        builder.addFieldInt32(4, enum2, foobar_class_.arguments_);
    }
    static addEnum3(builder, enum3) {
        builder.addFieldInt32(5, enum3, Abc.a);
    }
    static addReflect(builder, reflectOffset) {
        builder.addFieldOffset(6, reflectOffset, 0);
    }
    static endObject(builder) {
        const offset = builder.endObject();
        return offset;
    }
    unpack() {
        return new Object_T(this.return_(), this.if_(), this.switch_(), this.enum_(), this.enum2(), this.enum3(), (this.reflect() !== null ? this.reflect().unpack() : null));
    }
    unpackTo(_o) {
        _o.return_ = this.return_();
        _o.if_ = this.if_();
        _o.switch_ = this.switch_();
        _o.enum_ = this.enum_();
        _o.enum2 = this.enum2();
        _o.enum3 = this.enum3();
        _o.reflect = (this.reflect() !== null ? this.reflect().unpack() : null);
    }
}
export class Object_T {
    constructor(return_ = 0, if_ = 0, switch_ = 0, enum_ = class_.new_, enum2 = foobar_class_.arguments_, enum3 = Abc.a, reflect = null) {
        this.return_ = return_;
        this.if_ = if_;
        this.switch_ = switch_;
        this.enum_ = enum_;
        this.enum2 = enum2;
        this.enum3 = enum3;
        this.reflect = reflect;
    }
    pack(builder) {
        const reflect = (this.reflect !== null ? this.reflect.pack(builder) : 0);
        Object_.startObject(builder);
        Object_.addReturn(builder, this.return_);
        Object_.addIf(builder, this.if_);
        Object_.addSwitch(builder, this.switch_);
        Object_.addEnum(builder, this.enum_);
        Object_.addEnum2(builder, this.enum2);
        Object_.addEnum3(builder, this.enum3);
        Object_.addReflect(builder, reflect);
        return Object_.endObject(builder);
    }
}
