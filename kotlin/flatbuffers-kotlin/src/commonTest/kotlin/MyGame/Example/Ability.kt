// automatically generated by the FlatBuffers compiler, do not modify

package MyGame.Example

import com.google.flatbuffers.kotlin.*
@Suppress("unused")
class Ability : Struct() {

    fun init(i: Int, buffer: ReadWriteBuffer) : Ability = reset(i, buffer)
    fun assign(i: Int, buffer: ReadWriteBuffer) : Ability = init(i, buffer)

    val id : UInt get() = bb.getInt(bufferPos + 0).toUInt()

    val distance : UInt get() = bb.getInt(bufferPos + 4).toUInt()

    companion object {

        fun createAbility(builder: FlatBufferBuilder, id: UInt, distance: UInt) : Int {
            builder.prep(4, 8)
            builder.putInt(distance.toInt())
            builder.putInt(id.toInt())
            return builder.offset()
        }
    }
}
