// automatically generated by the FlatBuffers compiler, do not modify

import com.google.flatbuffers.kotlin.*
@Suppress("unused")
class FallingTub : Struct() {

    fun init(i: Int, buffer: ReadWriteBuffer) : FallingTub = reset(i, buffer)
    fun assign(i: Int, buffer: ReadWriteBuffer) : FallingTub = init(i, buffer)

    val weight : Int get() = bb.getInt(bufferPos + 0)

    companion object {

        fun createFallingTub(builder: FlatBufferBuilder, weight: Int) : Int {
            builder.prep(4, 4)
            builder.putInt(weight)
            return builder.offset()
        }
    }
}
