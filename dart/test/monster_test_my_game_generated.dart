// automatically generated by the FlatBuffers compiler, do not modify
// ignore_for_file: unused_import, unused_field, unused_element, unused_local_variable

library my_game;

import 'dart:typed_data' show Uint8List;
import 'package:flat_buffers/flat_buffers.dart' as fb;

import './monster_test_my_game.example_generated.dart' as my_game_example;
import './monster_test_my_game.example2_generated.dart' as my_game_example2;

class InParentNamespace {
  InParentNamespace._(this._bc, this._bcOffset);
  factory InParentNamespace(List<int> bytes) {
    fb.BufferContext rootRef = new fb.BufferContext.fromBytes(bytes);
    return reader.read(rootRef, 0);
  }

  static const fb.Reader<InParentNamespace> reader = const _InParentNamespaceReader();

  final fb.BufferContext _bc;
  final int _bcOffset;


  @override
  String toString() {
    return 'InParentNamespace{}';
  }

  InParentNamespaceT unpack() => InParentNamespaceT();

  static int pack(fb.Builder fbBuilder, InParentNamespaceT? object) {
    if (object == null) return 0;
    return object.pack(fbBuilder);
  }
}

class InParentNamespaceT {
  int pack(fb.Builder fbBuilder) {
    fbBuilder.startTable();
    return fbBuilder.endTable();
  }

  @override
  String toString() {
    return 'InParentNamespaceT{}';
  }
}

class _InParentNamespaceReader extends fb.TableReader<InParentNamespace> {
  const _InParentNamespaceReader();

  @override
  InParentNamespace createObject(fb.BufferContext bc, int offset) => 
    new InParentNamespace._(bc, offset);
}

class InParentNamespaceObjectBuilder extends fb.ObjectBuilder {

  InParentNamespaceObjectBuilder();

  /// Finish building, and store into the [fbBuilder].
  @override
  int finish(fb.Builder fbBuilder) {
    fbBuilder.startTable();
    return fbBuilder.endTable();
  }

  /// Convenience method to serialize to byte list.
  @override
  Uint8List toBytes([String? fileIdentifier]) {
    fb.Builder fbBuilder = new fb.Builder(deduplicateTables: false);
    int offset = finish(fbBuilder);
    fbBuilder.finish(offset, fileIdentifier);
    return fbBuilder.buffer;
  }
}
