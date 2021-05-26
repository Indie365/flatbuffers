// automatically generated by the FlatBuffers compiler, do not modify
// ignore_for_file: unused_import, unused_field, unused_local_variable

library namespace_c;

import 'dart:typed_data' show Uint8List;
import 'package:flat_buffers/flat_buffers.dart' as fb;

import './namespace_test2_namespace_a_generated.dart' as namespace_a;

class TableInC {
  TableInC._(this._bc, this._bcOffset);
  factory TableInC(List<int> bytes) {
    fb.BufferContext rootRef = new fb.BufferContext.fromBytes(bytes);
    return reader.read(rootRef, 0);
  }

  static const fb.Reader<TableInC> reader = const _TableInCReader();

  final fb.BufferContext _bc;
  final int _bcOffset;

  namespace_a.TableInFirstNS get referToA1 => namespace_a.TableInFirstNS.reader.vTableGet(_bc, _bcOffset, 4, null);
  namespace_a.SecondTableInA get referToA2 => namespace_a.SecondTableInA.reader.vTableGet(_bc, _bcOffset, 6, null);

  @override
  String toString() {
    return 'TableInC{referToA1: $referToA1, referToA2: $referToA2}';
  }
}

class _TableInCReader extends fb.TableReader<TableInC> {
  const _TableInCReader();

  @override
  TableInC createObject(fb.BufferContext bc, int offset) => 
    new TableInC._(bc, offset);
}

class TableInCBuilder {
  TableInCBuilder(this.fbBuilder) {
    assert(fbBuilder != null);
  }

  final fb.Builder fbBuilder;

  void begin() {
    fbBuilder.startTable();
  }

  int addReferToA1Offset(int offset) {
    fbBuilder.addOffset(0, offset);
    return fbBuilder.offset;
  }
  int addReferToA2Offset(int offset) {
    fbBuilder.addOffset(1, offset);
    return fbBuilder.offset;
  }

  int finish() {
    return fbBuilder.endTable();
  }
}

class TableInCObjectBuilder extends fb.ObjectBuilder {
  final namespace_a.TableInFirstNSObjectBuilder _referToA1;
  final namespace_a.SecondTableInAObjectBuilder _referToA2;

  TableInCObjectBuilder({
    required namespace_a.TableInFirstNSObjectBuilder referToA1,
    required namespace_a.SecondTableInAObjectBuilder referToA2,
  })
      : _referToA1 = referToA1,
        _referToA2 = referToA2;

  /// Finish building, and store into the [fbBuilder].
  @override
  int finish(
    fb.Builder fbBuilder) {
    assert(fbBuilder != null);
    final int referToA1Offset = _referToA1?.getOrCreateOffset(fbBuilder);
    final int referToA2Offset = _referToA2?.getOrCreateOffset(fbBuilder);

    fbBuilder.startTable();
    if (referToA1Offset != null) {
      fbBuilder.addOffset(0, referToA1Offset);
    }
    if (referToA2Offset != null) {
      fbBuilder.addOffset(1, referToA2Offset);
    }
    return fbBuilder.endTable();
  }

  /// Convenience method to serialize to byte list.
  @override
  Uint8List toBytes([String? fileIdentifier]) {
    fb.Builder fbBuilder = new fb.Builder();
    int offset = finish(fbBuilder);
    return fbBuilder.finish(offset, fileIdentifier);
  }
}
