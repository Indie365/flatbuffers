// automatically generated by the FlatBuffers compiler, do not modify

package NamespaceA.NamespaceB

import com.google.flatbuffers.kotlin.*
@Suppress("unused")
class TableInNestedNS : Table() {

    fun init(i: Int, buffer: ReadWriteBuffer) : TableInNestedNS = reset(i, buffer)
    fun assign(i: Int, buffer: ReadWriteBuffer) : TableInNestedNS = init(i, buffer)

    val foo : Int get() = lookupField(4, 0 ) { bb.getInt(it + bufferPos) }

    companion object {
        fun validateVersion() = VERSION_2_0_8

        fun asRoot(buffer: ReadWriteBuffer) : TableInNestedNS = asRoot(buffer, TableInNestedNS())
        fun asRoot(buffer: ReadWriteBuffer, obj: TableInNestedNS) : TableInNestedNS = obj.assign(buffer.getInt(buffer.limit) + buffer.limit, buffer)


        fun createTableInNestedNS(builder: FlatBufferBuilder, foo: Int) : Int {
            builder.startTable(1)
            addFoo(builder, foo)
            return endTableInNestedNS(builder)
        }
        fun startTableInNestedNS(builder: FlatBufferBuilder) = builder.startTable(1)

        fun addFoo(builder: FlatBufferBuilder, foo: Int) = builder.add(0, foo, 0)

        fun endTableInNestedNS(builder: FlatBufferBuilder) : Int {
            val o = builder.endTable()
            return o
        }
    }
}
