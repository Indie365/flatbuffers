# automatically generated by the FlatBuffers compiler, do not modify

# module: NamespaceA

import ..NamespaceC
import FlatBuffers

FlatBuffers.@with_kw mutable struct SecondTableInA
    refer_to_c::Union{NamespaceC.TableInC, Nothing} = nothing
end
FlatBuffers.@ALIGN(SecondTableInA, 1)
FlatBuffers.slot_offsets(::Type{T}) where {T<:SecondTableInA} = [
    0x00000004
]

SecondTableInA(buf::AbstractVector{UInt8}) = FlatBuffers.read(SecondTableInA, buf)
SecondTableInA(io::IO) = FlatBuffers.deserialize(io, SecondTableInA)
