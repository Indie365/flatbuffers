// automatically generated by the FlatBuffers compiler, do not modify

import com.google.flatbuffers.kotlin.*
@Suppress("unused")
class HandFan : Table() {

    fun init(i: Int, buffer: ReadWriteBuffer) : HandFan = reset(i, buffer)
    fun assign(i: Int, buffer: ReadWriteBuffer) : HandFan = init(i, buffer)

    val length : Int get() = lookupField(4, 0 ) { bb.getInt(it + bufferPos) }

    companion object {
        fun validateVersion() = VERSION_2_0_8

        fun asRoot(buffer: ReadWriteBuffer) : HandFan = asRoot(buffer, HandFan())
        fun asRoot(buffer: ReadWriteBuffer, obj: HandFan) : HandFan = obj.assign(buffer.getInt(buffer.limit) + buffer.limit, buffer)


        fun createHandFan(builder: FlatBufferBuilder, length: Int) : Int {
            builder.startTable(1)
            addLength(builder, length)
            return endHandFan(builder)
        }
        fun startHandFan(builder: FlatBufferBuilder) = builder.startTable(1)

        fun addLength(builder: FlatBufferBuilder, length: Int) = builder.add(0, length, 0)

        fun endHandFan(builder: FlatBufferBuilder) : Int {
            val o = builder.endTable()
            return o
        }
    }
}
