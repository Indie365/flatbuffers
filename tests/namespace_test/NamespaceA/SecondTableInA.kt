// automatically generated by the FlatBuffers compiler, do not modify

package NamespaceA

import java.nio.*
import kotlin.math.sign
import com.google.flatbuffers.*

@Suppress("unused")
@ExperimentalUnsignedTypes
class SecondTableInA : Table() {

    fun __init(_i: Int, _bb: ByteBuffer)  {
        __reset(_i, _bb)
    }
    fun __assign(_i: Int, _bb: ByteBuffer) : SecondTableInA {
        __init(_i, _bb)
        return this
    }
    val referToC : NamespaceC.TableInC? get() = referToC(NamespaceC.TableInC())
    fun referToC(obj: NamespaceC.TableInC) : NamespaceC.TableInC? {
        val o = __offset(4)
        return if (o != 0) {
            obj.__assign(__indirect(o + bb_pos), bb)
        } else {
            null
        }
    }
    companion object {
        fun validateVersion() = Constants.FLATBUFFERS_22_11_23()
        fun getRootAsSecondTableInA(_bb: ByteBuffer): SecondTableInA = getRootAsSecondTableInA(_bb, SecondTableInA())
        fun getRootAsSecondTableInA(_bb: ByteBuffer, obj: SecondTableInA): SecondTableInA {
            _bb.order(ByteOrder.LITTLE_ENDIAN)
            return (obj.__assign(_bb.getInt(_bb.position()) + _bb.position(), _bb))
        }
        fun createSecondTableInA(builder: FlatBufferBuilder, referToCOffset: Int) : Int {
            builder.startTable(1)
            addReferToC(builder, referToCOffset)
            return endSecondTableInA(builder)
        }
        fun startSecondTableInA(builder: FlatBufferBuilder) = builder.startTable(1)
        fun addReferToC(builder: FlatBufferBuilder, referToC: Int) = builder.addOffset(0, referToC, 0)
        fun endSecondTableInA(builder: FlatBufferBuilder) : Int {
            val o = builder.endTable()
            return o
        }
    }
}
