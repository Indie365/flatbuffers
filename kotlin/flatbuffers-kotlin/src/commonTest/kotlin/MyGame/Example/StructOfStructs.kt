// automatically generated by the FlatBuffers compiler, do not modify

package MyGame.Example

import com.google.flatbuffers.kotlin.*
@Suppress("unused")
class StructOfStructs : Struct() {

    fun init(i: Int, buffer: ReadWriteBuffer) : StructOfStructs = reset(i, buffer)
    fun assign(i: Int, buffer: ReadWriteBuffer) : StructOfStructs = init(i, buffer)

    val a : MyGame.Example.Ability? get() = a(MyGame.Example.Ability())
    fun a(obj: MyGame.Example.Ability) : MyGame.Example.Ability? = obj.assign(bufferPos + 0, bb)

    val b : MyGame.Example.Test? get() = b(MyGame.Example.Test())
    fun b(obj: MyGame.Example.Test) : MyGame.Example.Test? = obj.assign(bufferPos + 8, bb)

    val c : MyGame.Example.Ability? get() = c(MyGame.Example.Ability())
    fun c(obj: MyGame.Example.Ability) : MyGame.Example.Ability? = obj.assign(bufferPos + 12, bb)

    companion object {

        fun createStructOfStructs(builder: FlatBufferBuilder, a_id: UInt, a_distance: UInt, b_a: Short, b_b: Byte, c_id: UInt, c_distance: UInt) : Int {
            builder.prep(4, 20)
            builder.prep(4, 8)
            builder.putInt(c_distance.toInt())
            builder.putInt(c_id.toInt())
            builder.prep(2, 4)
            builder.pad(1)
            builder.putByte(b_b)
            builder.putShort(b_a)
            builder.prep(4, 8)
            builder.putInt(a_distance.toInt())
            builder.putInt(a_id.toInt())
            return builder.offset()
        }
    }
}
