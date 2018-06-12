// automatically generated by the FlatBuffers compiler, do not modify
// ignore_for_file: unused_import, unused_field, unused_local_variable

library namespace_a.namespace_b;

import 'dart:typed_data' show Uint8List;
import 'package:flat_buffers/flat_buffers.dart' as fb;


class EnumInNestedNS {
  final int value;
  const EnumInNestedNS._(this.value);

  factory EnumInNestedNS.fromValue(int value) {
    if (value == null) return null;
    if (!values.containsKey(value)) {
      throw new StateError('Invalid value $value for bit flag enum EnumInNestedNS');
    }
    return values[value];
  }

  static const int minValue = 0;
  static const int maxValue = 2;
  static bool containsValue(int value) => values.containsKey(value);

  static const EnumInNestedNS A = const EnumInNestedNS._(0);
  static const EnumInNestedNS B = const EnumInNestedNS._(1);
  static const EnumInNestedNS C = const EnumInNestedNS._(2);
  static get values => {0: A,1: B,2: C,};

  static const fb.Reader<EnumInNestedNS> reader = const _EnumInNestedNSReader();

  @override
  String toString() {
    return 'EnumInNestedNS{value: $value}';
  }
}

class _EnumInNestedNSReader extends fb.Reader<EnumInNestedNS> {
  const _EnumInNestedNSReader();

  @override
  int get size => 1;

  @override
  EnumInNestedNS read(fb.BufferContext bc, int offset) =>
      new EnumInNestedNS.fromValue(const fb.Int8Reader().read(bc, offset));
}

class TableInNestedNS {
  TableInNestedNS._(this._bc, this._bcOffset);
  factory TableInNestedNS(List<int> bytes) {
    fb.BufferContext rootRef = new fb.BufferContext.fromBytes(bytes);
    return reader.read(rootRef, 0);
  }

  static const fb.Reader<TableInNestedNS> reader = const _TableInNestedNSReader();

  final fb.BufferContext _bc;
  final int _bcOffset;

  int get foo => const fb.Int32Reader().vTableGet(_bc, _bcOffset, 4, null);

  @override
  String toString() {
    return 'TableInNestedNS{foo: $foo}';
  }
}

class _TableInNestedNSReader extends fb.TableReader<TableInNestedNS> {
  const _TableInNestedNSReader();

  @override
  TableInNestedNS createObject(fb.BufferContext bc, int offset) => 
    new TableInNestedNS._(bc, offset);
}

class TableInNestedNSBuilder {
  TableInNestedNSBuilder(this.fbBuilder) {
    assert(fbBuilder != null);
  }

  final fb.Builder fbBuilder;

  void begin() {
    fbBuilder.startTable();
  }

  int addFoo(int foo) {
    fbBuilder.addInt32(0, foo);
    return fbBuilder.offset;
  }

  int finish() {
    return fbBuilder.endTable();
  }
}

class TableInNestedNSObjectBuilder extends fb.ObjectBuilder {
  final int _foo;

  TableInNestedNSObjectBuilder({
    int foo,
  })
      : _foo = foo;

  /// Finish building, and store into the [fbBuilder].
  @override
  int finish(
    fb.Builder fbBuilder) {
    assert(fbBuilder != null);

    fbBuilder.startTable();
    fbBuilder.addInt32(0, _foo);
    return fbBuilder.endTable();
  }

  /// Convenience method to serialize to byte list.
  @override
  Uint8List toBytes([String fileIdentifier]) {
    fb.Builder fbBuilder = new fb.Builder();
    int offset = finish(fbBuilder);
    return fbBuilder.finish(offset, fileIdentifier);
  }
}
class StructInNestedNS {
  StructInNestedNS._(this._bc, this._bcOffset);

  static const fb.Reader<StructInNestedNS> reader = const _StructInNestedNSReader();

  final fb.BufferContext _bc;
  final int _bcOffset;

  int get a => const fb.Int32Reader().read(_bc, _bcOffset + 0);
  int get b => const fb.Int32Reader().read(_bc, _bcOffset + 4);

  @override
  String toString() {
    return 'StructInNestedNS{a: $a, b: $b}';
  }
}

class _StructInNestedNSReader extends fb.StructReader<StructInNestedNS> {
  const _StructInNestedNSReader();

  @override
  int get size => 8;

  @override
  StructInNestedNS createObject(fb.BufferContext bc, int offset) => 
    new StructInNestedNS._(bc, offset);
}

class StructInNestedNSBuilder {
  StructInNestedNSBuilder(this.fbBuilder) {
    assert(fbBuilder != null);
  }

  final fb.Builder fbBuilder;

  int finish(int a, int b) {
    fbBuilder.putInt32(b);
    fbBuilder.putInt32(a);
    return fbBuilder.offset;
  }

}

class StructInNestedNSObjectBuilder extends fb.ObjectBuilder {
  final int _a;
  final int _b;

  StructInNestedNSObjectBuilder({
    int a,
    int b,
  })
      : _a = a,
        _b = b;

  /// Finish building, and store into the [fbBuilder].
  @override
  int finish(
    fb.Builder fbBuilder) {
    assert(fbBuilder != null);

    fbBuilder.putInt32(_b);
    fbBuilder.putInt32(_a);
    return fbBuilder.offset;
  }

  /// Convenience method to serialize to byte list.
  @override
  Uint8List toBytes([String fileIdentifier]) {
    fb.Builder fbBuilder = new fb.Builder();
    int offset = finish(fbBuilder);
    return fbBuilder.finish(offset, fileIdentifier);
  }
}
