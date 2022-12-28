// automatically generated by the FlatBuffers compiler, do not modify

package MyGame.Example

import com.google.flatbuffers.kotlin.*
@Suppress("unused")
class TypeAliases : Table() {

    fun init(i: Int, buffer: ReadWriteBuffer) : TypeAliases = reset(i, buffer)
    fun assign(i: Int, buffer: ReadWriteBuffer) : TypeAliases = init(i, buffer)

    val i8 : Byte get() = lookupField(4, 0 ) { bb.get(it + bufferPos) }

    val u8 : UByte get() = lookupField(6, 0u ) { bb.getUByte(it + bufferPos) }

    val i16 : Short get() = lookupField(8, 0 ) { bb.getShort(it + bufferPos) }

    val u16 : UShort get() = lookupField(10, 0u ) { bb.getUShort(it + bufferPos) }

    val i32 : Int get() = lookupField(12, 0 ) { bb.getInt(it + bufferPos) }

    val u32 : UInt get() = lookupField(14, 0u ) { bb.getUInt(it + bufferPos) }

    val i64 : Long get() = lookupField(16, 0L ) { bb.getLong(it + bufferPos) }

    val u64 : ULong get() = lookupField(18, 0UL ) { bb.getULong(it + bufferPos) }

    val f32 : Float get() = lookupField(20, 0.0f ) { bb.getFloat(it + bufferPos) }

    val f64 : Double get() = lookupField(22, 0.0 ) { bb.getDouble(it + bufferPos) }

    fun v8(j: Int) : Byte = lookupField(24, 0 ) { bb.get(vector(it) + j * 1) }
    val v8Length : Int get() = lookupField(24, 0 ) { vectorLength(it) }
    fun v8AsBuffer() : ReadBuffer = vectorAsBuffer(bb, 24, 1)

    fun vf64(j: Int) : Double = lookupField(26, 0.0 ) { bb.getDouble(vector(it) + j * 8) }
    val vf64Length : Int get() = lookupField(26, 0 ) { vectorLength(it) }
    fun vf64AsBuffer() : ReadBuffer = vectorAsBuffer(bb, 26, 8)

    companion object {
        fun validateVersion() = VERSION_2_0_8

        fun asRoot(buffer: ReadWriteBuffer) : TypeAliases = asRoot(buffer, TypeAliases())
        fun asRoot(buffer: ReadWriteBuffer, obj: TypeAliases) : TypeAliases = obj.assign(buffer.getInt(buffer.limit) + buffer.limit, buffer)


        fun createTypeAliases(builder: FlatBufferBuilder, i8: Byte, u8: UByte, i16: Short, u16: UShort, i32: Int, u32: UInt, i64: Long, u64: ULong, f32: Float, f64: Double, v8Offset: ArrayOffset<Byte>, vf64Offset: ArrayOffset<Double>) : Offset<TypeAliases> {
            builder.startTable(12)
            addF64(builder, f64)
            addU64(builder, u64)
            addI64(builder, i64)
            addVf64(builder, vf64Offset)
            addV8(builder, v8Offset)
            addF32(builder, f32)
            addU32(builder, u32)
            addI32(builder, i32)
            addU16(builder, u16)
            addI16(builder, i16)
            addU8(builder, u8)
            addI8(builder, i8)
            return endTypeAliases(builder)
        }
        fun startTypeAliases(builder: FlatBufferBuilder) = builder.startTable(12)

        fun addI8(builder: FlatBufferBuilder, i8: Byte) = builder.add(0, i8, 0)

        fun addU8(builder: FlatBufferBuilder, u8: UByte) = builder.add(1, u8, 0)

        fun addI16(builder: FlatBufferBuilder, i16: Short) = builder.add(2, i16, 0)

        fun addU16(builder: FlatBufferBuilder, u16: UShort) = builder.add(3, u16, 0)

        fun addI32(builder: FlatBufferBuilder, i32: Int) = builder.add(4, i32, 0)

        fun addU32(builder: FlatBufferBuilder, u32: UInt) = builder.add(5, u32, 0)

        fun addI64(builder: FlatBufferBuilder, i64: Long) = builder.add(6, i64, 0L)

        fun addU64(builder: FlatBufferBuilder, u64: ULong) = builder.add(7, u64, 0)

        fun addF32(builder: FlatBufferBuilder, f32: Float) = builder.add(8, f32, 0.0)

        fun addF64(builder: FlatBufferBuilder, f64: Double) = builder.add(9, f64, 0.0)

        fun addV8(builder: FlatBufferBuilder, v8: ArrayOffset<Byte>) = builder.addOffset(10, v8, null)

        fun createV8Vector(builder: FlatBufferBuilder, data: ByteArray) : ArrayOffset<Byte> {
            builder.startVector(1, data.size, 1)
            for (i in data.size - 1 downTo 0) {
                builder.add(data[i])
            }
            return builder.endVector()
        }

        fun startV8Vector(builder: FlatBufferBuilder, numElems: Int) = builder.startVector(1, numElems, 1)

        fun addVf64(builder: FlatBufferBuilder, vf64: ArrayOffset<Double>) = builder.addOffset(11, vf64, null)

        fun createVf64Vector(builder: FlatBufferBuilder, data: DoubleArray) : ArrayOffset<Double> {
            builder.startVector(8, data.size, 8)
            for (i in data.size - 1 downTo 0) {
                builder.add(data[i])
            }
            return builder.endVector()
        }

        fun startVf64Vector(builder: FlatBufferBuilder, numElems: Int) = builder.startVector(8, numElems, 8)

        fun endTypeAliases(builder: FlatBufferBuilder) : Offset<TypeAliases> {
            val o: Offset<TypeAliases> = builder.endTable()
            return o
        }
    }
}
