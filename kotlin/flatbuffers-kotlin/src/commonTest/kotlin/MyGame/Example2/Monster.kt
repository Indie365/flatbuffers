// automatically generated by the FlatBuffers compiler, do not modify

package MyGame.Example2

import com.google.flatbuffers.kotlin.*
@Suppress("unused")
class Monster : Table() {

    fun init(i: Int, buffer: ReadWriteBuffer) : Monster = reset(i, buffer)
    fun assign(i: Int, buffer: ReadWriteBuffer) : Monster = init(i, buffer)

    companion object {
        fun validateVersion() = VERSION_2_0_8

        fun asRoot(buffer: ReadWriteBuffer) : Monster = asRoot(buffer, Monster())
        fun asRoot(buffer: ReadWriteBuffer, obj: Monster) : Monster = obj.assign(buffer.getInt(buffer.limit) + buffer.limit, buffer)


        fun startMonster(builder: FlatBufferBuilder) = builder.startTable(0)

        fun endMonster(builder: FlatBufferBuilder) : Int {
            val o = builder.endTable()
            return o
        }
    }
}
