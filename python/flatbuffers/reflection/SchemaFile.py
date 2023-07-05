# automatically generated by the FlatBuffers compiler, do not modify

# namespace: reflection

import flatbuffers
from flatbuffers.compat import import_numpy
np = import_numpy()

# File specific information.
# Symbols declared within a file may be recovered by iterating over all
# symbols and examining the `declaration_file` field.
class SchemaFile(object):
    __slots__ = ['_tab']

    @classmethod
    def GetRootAs(cls, buf, offset=0):
        n = flatbuffers.encode.Get(flatbuffers.packer.uoffset, buf, offset)
        x = SchemaFile()
        x.Init(buf, n + offset)
        return x

    @classmethod
    def GetRootAsSchemaFile(cls, buf, offset=0):
        """This method is deprecated. Please switch to GetRootAs."""
        return cls.GetRootAs(buf, offset)

    @classmethod
    def SchemaFileBufferHasIdentifier(cls, buf, offset, size_prefixed=False):
        return flatbuffers.util.BufferHasIdentifier(buf, offset, b"\x42\x46\x42\x53", size_prefixed=size_prefixed)


    @classmethod
    def VerifySchemaFile(cls, buf, offset=0, size_prefixed=False):
        return flatbuffers.NewVerifier(buf, offset).VerifyBuffer(b"\x42\x46\x42\x53", size_prefixed, SchemaFileVerify)

    # SchemaFile
    def Init(self, buf, pos):
        self._tab = flatbuffers.table.Table(buf, pos)

    # Filename, relative to project root.
    # SchemaFile
    def Filename(self):
        o = flatbuffers.number_types.UOffsetTFlags.py_type(self._tab.Offset(4))
        if o != 0:
            return self._tab.String(o + self._tab.Pos)
        return None

    # Names of included files, relative to project root.
    # SchemaFile
    def IncludedFilenames(self, j):
        o = flatbuffers.number_types.UOffsetTFlags.py_type(self._tab.Offset(6))
        if o != 0:
            a = self._tab.Vector(o)
            return self._tab.String(a + flatbuffers.number_types.UOffsetTFlags.py_type(j * 4))
        return ""

    # SchemaFile
    def IncludedFilenamesLength(self):
        o = flatbuffers.number_types.UOffsetTFlags.py_type(self._tab.Offset(6))
        if o != 0:
            return self._tab.VectorLen(o)
        return 0

    # SchemaFile
    def IncludedFilenamesIsNone(self):
        o = flatbuffers.number_types.UOffsetTFlags.py_type(self._tab.Offset(6))
        return o == 0

def SchemaFileStart(builder):
    builder.StartObject(2)

def Start(builder):
    SchemaFileStart(builder)

def SchemaFileAddFilename(builder, filename):
    builder.PrependUOffsetTRelativeSlot(0, flatbuffers.number_types.UOffsetTFlags.py_type(filename), 0)

def AddFilename(builder, filename):
    SchemaFileAddFilename(builder, filename)

def SchemaFileAddIncludedFilenames(builder, includedFilenames):
    builder.PrependUOffsetTRelativeSlot(1, flatbuffers.number_types.UOffsetTFlags.py_type(includedFilenames), 0)

def AddIncludedFilenames(builder, includedFilenames):
    SchemaFileAddIncludedFilenames(builder, includedFilenames)

def SchemaFileStartIncludedFilenamesVector(builder, numElems):
    return builder.StartVector(4, numElems, 4)

def StartIncludedFilenamesVector(builder, numElems: int) -> int:
    return SchemaFileStartIncludedFilenamesVector(builder, numElems)

def SchemaFileEnd(builder):
    return builder.EndObject()

def End(builder):
    return SchemaFileEnd(builder)


# Verification function for 'SchemaFile' table.
def SchemaFileVerify(verifier, pos):
    result = True
    result = result and verifier.VerifyTableStart(pos)
    result = result and verifier.VerifyString(pos, 4, True) # field: filename, type: [string]
    result = result and verifier.VerifyVectorOfStrings(pos, 6, False)  # field: includedFilenames, type: [string]
    result = result and verifier.VerifyTableEnd(pos)
    return result

