// automatically generated by the FlatBuffers compiler, do not modify

import com.google.flatbuffers.kotlin.*
@Suppress("unused")
class BookReader : Struct() {

    fun init(i: Int, buffer: ReadWriteBuffer) : BookReader = reset(i, buffer)
    fun assign(i: Int, buffer: ReadWriteBuffer) : BookReader = init(i, buffer)

    val booksRead : Int get() = bb.getInt(bufferPos + 0)

    companion object {

        fun createBookReader(builder: FlatBufferBuilder, booksRead: Int) : Int {
            builder.prep(4, 4)
            builder.putInt(booksRead)
            return builder.offset()
        }
    }
}
