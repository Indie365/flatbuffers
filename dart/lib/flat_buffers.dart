// Copyright (c) 2016, the Dart project authors.  Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

import 'dart:collection';
import 'dart:convert';
import 'dart:math';
import 'dart:typed_data';

const int _sizeofUint8 = 1;
const int _sizeofUint16 = 2;
const int _sizeofUint32 = 4;
const int _sizeofUint64 = 8;
const int _sizeofInt8 = 1;
const int _sizeofInt16 = 2;
const int _sizeofInt32 = 4;
const int _sizeofInt64 = 8;
const int _sizeofFloat32 = 4;
const int _sizeofFloat64 = 8;

/// Callback used to invoke a struct builder's finish method.
///
/// This callback is used by other struct's `finish` methods to write the nested
/// struct's fields inline.
typedef void StructBuilder();

/// Buffer with data and some context about it.
class BufferContext {
  final ByteData _buffer;

  factory BufferContext.fromBytes(List<int> byteList) {
    Uint8List uint8List = _asUint8List(byteList);
    ByteData buf = new ByteData.view(uint8List.buffer, uint8List.offsetInBytes);
    return new BufferContext._(buf);
  }

  BufferContext._(this._buffer);

  int derefObject(int offset) {
    return offset + _getUint32(offset);
  }

  Uint8List _asUint8LIst(int offset, int length) =>
      _buffer.buffer.asUint8List(_buffer.offsetInBytes + offset, length);

  double _getFloat64(int offset) =>
      _buffer.getFloat64(offset, Endian.little);

  double _getFloat32(int offset) =>
      _buffer.getFloat32(offset, Endian.little);

  int _getInt64(int offset) =>
      _buffer.getInt64(offset, Endian.little);

  int _getInt32(int offset) =>
      _buffer.getInt32(offset, Endian.little);

  int _getInt16(int offset) =>
      _buffer.getInt16(offset, Endian.little);

  int _getInt8(int offset) => _buffer.getInt8(offset);

  int _getUint64(int offset) =>
      _buffer.getUint64(offset, Endian.little);

  int _getUint32(int offset) =>
      _buffer.getUint32(offset, Endian.little);

  int _getUint16(int offset) =>
      _buffer.getUint16(offset, Endian.little);

  int _getUint8(int offset) => _buffer.getUint8(offset);

  /// If the [byteList] is already a [Uint8List] return it.
  /// Otherwise return a [Uint8List] copy of the [byteList].
  static Uint8List _asUint8List(List<int> byteList) {
    if (byteList is Uint8List) {
      return byteList;
    } else {
      return new Uint8List.fromList(byteList);
    }
  }
}

/// Class implemented by typed builders generated by flatc.
abstract class ObjectBuilder {
  int _firstOffset;

  /// Can be used to write the data represented by this builder to the [Builder]
  /// and reuse the offset created in multiple tables.
  ///
  /// Note that this method assumes you call it using the same [Builder] instance
  /// every time. The returned offset is only good for the [Builder] used in the
  /// first call to this method.
  int getOrCreateOffset(Builder fbBuilder) {
    _firstOffset ??= finish(fbBuilder);
    return _firstOffset;
  }

  /// Writes the data in this helper to the [Builder].
  int finish(Builder fbBuilder);

  /// Convenience method that will create a new [Builder], [finish]es the data,
  /// and returns the buffer as a [Uint8List] of bytes.
  Uint8List toBytes();
}

/// Class that helps building flat buffers.
class Builder {
  final int initialSize;

  /// The list of existing VTable(s).
  //final List<_VTable> _vTables = <_VTable>[];
  final List<int> _vTables = <int>[];

  ByteData _buf;

  Allocator _allocator;

  /// The maximum alignment that has been seen so far.  If [_buf] has to be
  /// reallocated in the future (to insert room at its start for more bytes) the
  /// reallocation will need to be a multiple of this many bytes.
  int _maxAlign;

  /// The number of bytes that have been written to the buffer so far.  The
  /// most recently written byte is this many bytes from the end of [_buf].
  int _tail;

  /// The location of the end of the current table, measured in bytes from the
  /// end of [_buf], or `null` if a table is not currently being built.
  int _currentTableEndTail;

  _VTable _currentVTable;

  /// Map containing all strings that have been written so far.  This allows us
  /// to avoid duplicating strings.
  ///
  /// Allocated only if `internStrings` is set to true on the constructor.
  Map<String, int> _strings;

  /// Creates a new FlatBuffers Builder.
  ///
  /// `initialSize` is the initial array size in bytes.  The [Builder] will
  /// automatically grow the array if/as needed.  `internStrings`, if set to
  /// true, will cause [writeString] to pool strings in the buffer so that
  /// identical strings will always use the same offset in tables.
  Builder(
      {this.initialSize: 1024,
      bool internStrings = false,
      Allocator allocator = _defaultAllocator})
      : _allocator = allocator {
    if (internStrings == true) {
      _strings = new Map<String, int>();
    }
    reset();
  }

  /// Add the [field] with the given boolean [value].  The field is not added if
  /// the [value] is equal to [def].  Booleans are stored as 8-bit fields with
  /// `0` for `false` and `1` for `true`.
  void addBool(int field, bool value, [bool def]) {
    _ensureCurrentVTable();
    if (value != null && value != def) {
      _prepare(_sizeofUint8, 1);
      _trackField(field);
      _buf.setInt8(_buf.lengthInBytes - _tail, value ? 1 : 0);
    }
  }

  /// Add the [field] with the given 32-bit signed integer [value].  The field is
  /// not added if the [value] is equal to [def].
  void addInt32(int field, int value, [int def]) {
    _ensureCurrentVTable();
    if (value != null && value != def) {
      _prepare(_sizeofInt32, 1);
      _trackField(field);
      _setInt32AtTail(_buf, _tail, value);
    }
  }

  /// Add the [field] with the given 32-bit signed integer [value].  The field is
  /// not added if the [value] is equal to [def].
  void addInt16(int field, int value, [int def]) {
    _ensureCurrentVTable();
    if (value != null && value != def) {
      _prepare(_sizeofInt16, 1);
      _trackField(field);
      _setInt16AtTail(_buf, _tail, value);
    }
  }

  /// Add the [field] with the given 8-bit signed integer [value].  The field is
  /// not added if the [value] is equal to [def].
  void addInt8(int field, int value, [int def]) {
    _ensureCurrentVTable();
    if (value != null && value != def) {
      _prepare(_sizeofInt8, 1);
      _trackField(field);
      _setInt8AtTail(_buf, _tail, value);
    }
  }

  void addStruct(int field, int offset) {
    _ensureCurrentVTable();
    _trackField(field);
    _currentVTable.addField(field, offset);
  }

  /// Add the [field] referencing an object with the given [offset].
  void addOffset(int field, int offset) {
    _ensureCurrentVTable();
    if (offset != null) {
      _prepare(_sizeofUint32, 1);
      _trackField(field);
      _setUint32AtTail(_buf, _tail, _tail - offset);
    }
  }

  /// Add the [field] with the given 32-bit unsigned integer [value].  The field
  /// is not added if the [value] is equal to [def].
  void addUint32(int field, int value, [int def]) {
    _ensureCurrentVTable();
    if (value != null && value != def) {
      _prepare(_sizeofUint32, 1);
      _trackField(field);
      _setUint32AtTail(_buf, _tail, value);
    }
  }

  /// Add the [field] with the given 32-bit unsigned integer [value].  The field
  /// is not added if the [value] is equal to [def].
  void addUint16(int field, int value, [int def]) {
    _ensureCurrentVTable();
    if (value != null && value != def) {
      _prepare(_sizeofUint16, 1);
      _trackField(field);
      _setUint16AtTail(_buf, _tail, value);
    }
  }

  /// Add the [field] with the given 8-bit unsigned integer [value].  The field
  /// is not added if the [value] is equal to [def].
  void addUint8(int field, int value, [int def]) {
    _ensureCurrentVTable();
    if (value != null && value != def) {
      _prepare(_sizeofUint8, 1);
      _trackField(field);
      _setUint8AtTail(_buf, _tail, value);
    }
  }

  /// Add the [field] with the given 32-bit float [value].  The field
  /// is not added if the [value] is equal to [def].
  void addFloat32(int field, double value, [double def]) {
    _ensureCurrentVTable();
    if (value != null && value != def) {
      _prepare(_sizeofFloat32, 1);
      _trackField(field);
      _setFloat32AtTail(_buf, _tail, value);
    }
  }

  /// Add the [field] with the given 64-bit double [value].  The field
  /// is not added if the [value] is equal to [def].
  void addFloat64(int field, double value, [double def]) {
    _ensureCurrentVTable();
    if (value != null && value != def) {
      _prepare(_sizeofFloat64, 1);
      _trackField(field);
      _setFloat64AtTail(_buf, _tail, value);
    }
  }

  /// Add the [field] with the given 64-bit unsigned integer [value].  The field
  /// is not added if the [value] is equal to [def].
  void addUint64(int field, int value, [double def]) {
    _ensureCurrentVTable();
    if (value != null && value != def) {
      _prepare(_sizeofUint64, 1);
      _trackField(field);
      _setUint64AtTail(_buf, _tail, value);
    }
  }

  /// Add the [field] with the given 64-bit unsigned integer [value].  The field
  /// is not added if the [value] is equal to [def].
  void addInt64(int field, int value, [double def]) {
    _ensureCurrentVTable();
    if (value != null && value != def) {
      _prepare(_sizeofInt64, 1);
      _trackField(field);
      _setInt64AtTail(_buf, _tail, value);
    }
  }

  /// End the current table and return its offset.
  int endTable() {
    if (_currentVTable == null) {
      throw new StateError('Start a table before ending it.');
    }
    // Prepare for writing the VTable.
    _prepare(_sizeofInt32, 1);
    int tableTail = _tail;
    // Prepare the size of the current table.
    _currentVTable.tableSize = tableTail - _currentTableEndTail;
    // Prepare the VTable to use for the current table.
    int vTableTail;
    {
      _currentVTable.computeFieldOffsets(tableTail);
      // Try to find an existing compatible VTable.
      // Search backward - more likely to have recently used one
      for (int i = _vTables.length - 1; i >= 0; i--) {
        final int vt2Offset = _vTables[i];
        final int vt2Start = _buf.lengthInBytes - vt2Offset;
        final int vt2Size = _buf.getUint16(vt2Start, Endian.little);

        if (_currentVTable._vTableSize == vt2Size &&
            _currentVTable._offsetsMatch(vt2Start, _buf)) {
          vTableTail = vt2Offset;
          break;
        }
      }
      // Write a new VTable.
      if (vTableTail == null) {
        _prepare(_sizeofUint16, _currentVTable.numOfUint16);
        vTableTail = _tail;
        _currentVTable.tail = vTableTail;
        _currentVTable.output(_buf, _buf.lengthInBytes - _tail);
        _vTables.add(_currentVTable.tail);
      }
    }
    // Set the VTable offset.
    _setInt32AtTail(_buf, tableTail, vTableTail - tableTail);
    // Done with this table.
    _currentVTable = null;
    return tableTail;
  }

  /// This method low level method can be used to return a raw piece of the buffer
  /// after using the the put* methods.
  ///
  /// Most clients should prefer calling [finish].
  Uint8List lowFinish() {
    int alignedTail = _tail + ((-_tail) % _maxAlign);
    return _buf.buffer.asUint8List(_buf.lengthInBytes - alignedTail);
  }

  /// Finish off the creation of the buffer.  The given [offset] is used as the
  /// root object offset, and usually references directly or indirectly every
  /// written object.  If [fileIdentifier] is specified (and not `null`), it is
  /// interpreted as a 4-byte Latin-1 encoded string that should be placed at
  /// bytes 4-7 of the file.
  Uint8List finish(int offset, [String fileIdentifier]) {
    _prepare(max(_sizeofUint32, _maxAlign), fileIdentifier == null ? 1 : 2);
    int alignedTail = _tail + ((-_tail) % _maxAlign);
    _setUint32AtTail(_buf, alignedTail, alignedTail - offset);
    if (fileIdentifier != null) {
      for (int i = 0; i < 4; i++) {
        _setUint8AtTail(_buf, alignedTail - _sizeofUint32 - i,
            fileIdentifier.codeUnitAt(i));
      }
    }
    return _buf.buffer.asUint8List(_buf.lengthInBytes - alignedTail);
  }

  /// Writes a Float64 to the tail of the buffer after preparing space for it.
  ///
  /// Updates the [offset] pointer.  This method is intended for use when writing structs to the buffer.
  void putFloat64(double value) {
    _prepare(_sizeofFloat64, 1);
    _setFloat32AtTail(_buf, _tail, value);
  }

  /// Writes a Float32 to the tail of the buffer after preparing space for it.
  ///
  /// Updates the [offset] pointer.  This method is intended for use when writing structs to the buffer.
  void putFloat32(double value) {
    _prepare(_sizeofFloat32, 1);
    _setFloat32AtTail(_buf, _tail, value);
  }

  /// Writes a Int64 to the tail of the buffer after preparing space for it.
  ///
  /// Updates the [offset] pointer.  This method is intended for use when writing structs to the buffer.
  void putInt64(int value) {
    _prepare(_sizeofInt64, 1);
    _setInt64AtTail(_buf, _tail, value);
  }

  /// Writes a Uint32 to the tail of the buffer after preparing space for it.
  ///
  /// Updates the [offset] pointer.  This method is intended for use when writing structs to the buffer.
  void putInt32(int value) {
    _prepare(_sizeofInt32, 1);
    _setInt32AtTail(_buf, _tail, value);
  }

  /// Writes a Uint16 to the tail of the buffer after preparing space for it.
  ///
  /// Updates the [offset] pointer.  This method is intended for use when writing structs to the buffer.
  void putInt16(int value) {
    _prepare(_sizeofInt16, 1);
    _setInt16AtTail(_buf, _tail, value);
  }

  /// Writes a Uint8 to the tail of the buffer after preparing space for it.
  ///
  /// Updates the [offset] pointer.  This method is intended for use when writing structs to the buffer.
  void putInt8(int value) {
    _prepare(_sizeofInt8, 1);
    _buf.setInt8(_buf.lengthInBytes - _tail, value);
  }

  /// Writes a Uint64 to the tail of the buffer after preparing space for it.
  ///
  /// Updates the [offset] pointer.  This method is intended for use when writing structs to the buffer.
  void putUint64(int value) {
    _prepare(_sizeofUint64, 1);
    _setUint64AtTail(_buf, _tail, value);
  }

  /// Writes a Uint32 to the tail of the buffer after preparing space for it.
  ///
  /// Updates the [offset] pointer.  This method is intended for use when writing structs to the buffer.
  void putUint32(int value) {
    _prepare(_sizeofUint32, 1);
    _setUint32AtTail(_buf, _tail, value);
  }

  /// Writes a Uint16 to the tail of the buffer after preparing space for it.
  ///
  /// Updates the [offset] pointer.  This method is intended for use when writing structs to the buffer.
  void putUint16(int value) {
    _prepare(_sizeofUint16, 1);
    _setUint16AtTail(_buf, _tail, value);
  }

  /// Writes a Uint8 to the tail of the buffer after preparing space for it.
  ///
  /// Updates the [offset] pointer.  This method is intended for use when writing structs to the buffer.
  void putUint8(int value) {
    _prepare(_sizeofUint8, 1);
    _buf.setUint8(_buf.lengthInBytes - _tail, value);
  }

  /// Reset the builder and make it ready for filling a new buffer.
  void reset() {
    if (_buf == null) {
      _buf = _allocator.allocate(initialSize);
      _allocator.clear(_buf, true);
    } else {
      _allocator.clear(_buf, false);
    }
    _maxAlign = 1;
    _tail = 0;
    _currentVTable = null;
    _vTables.clear();
    if (_strings != null) {
      _strings = new Map<String, int>();
    }
  }

  /// Start a new table.  Must be finished with [endTable] invocation.
  void startTable() {
    if (_currentVTable != null) {
      throw new StateError('Inline tables are not supported.');
    }
    _currentVTable = new _VTable();
    _currentTableEndTail = _tail;
  }

  /// Finish a Struct vector.  Most callers should preferto use [writeListOfStructs].
  ///
  /// Most callers should prefer [writeListOfStructs].
  int endStructVector(int count) {
    putUint32(count);
    return _tail;
  }

  /// Writes a list of Structs to the buffer, returning the offset
  int writeListOfStructs(List<ObjectBuilder> structBuilders) {
    _ensureNoVTable();
    for (int i = structBuilders.length - 1; i >= 0; i--) {
      structBuilders[i].finish(this);
    }
    return endStructVector(structBuilders.length);
  }

  /// Write the given list of [values].
  int writeList(List<int> values) {
    _ensureNoVTable();
    _prepare(_sizeofUint32, 1 + values.length);
    final int result = _tail;
    int tail = _tail;
    _setUint32AtTail(_buf, tail, values.length);
    tail -= _sizeofUint32;
    for (int value in values) {
      _setUint32AtTail(_buf, tail, tail - value);
      tail -= _sizeofUint32;
    }
    return result;
  }

  /// Write the given list of 64-bit float [values].
  int writeListFloat64(List<double> values) {
    _ensureNoVTable();
    _prepare(_sizeofFloat64, values.length, additionalBytes: _sizeofUint32);
    final int result = _tail;
    int tail = _tail;
    _setUint32AtTail(_buf, tail, values.length);
    tail -= _sizeofUint32;
    for (double value in values) {
      _setFloat64AtTail(_buf, tail, value);
      tail -= _sizeofFloat64;
    }
    return result;
  }

  /// Write the given list of 32-bit float [values].
  int writeListFloat32(List<double> values) {
    _ensureNoVTable();
    _prepare(_sizeofFloat32, 1 + values.length);
    final int result = _tail;
    int tail = _tail;
    _setUint32AtTail(_buf, tail, values.length);
    tail -= _sizeofUint32;
    for (double value in values) {
      _setFloat32AtTail(_buf, tail, value);
      tail -= _sizeofFloat32;
    }
    return result;
  }

  /// Write the given list of signed 64-bit integer [values].
  int writeListInt64(List<int> values) {
    _ensureNoVTable();
    _prepare(_sizeofInt64, values.length, additionalBytes: _sizeofUint32);
    final int result = _tail;
    int tail = _tail;
    _setUint32AtTail(_buf, tail, values.length);
    tail -= _sizeofUint32;
    for (int value in values) {
      _setInt64AtTail(_buf, tail, value);
      tail -= _sizeofInt64;
    }
    return result;
  }

  /// Write the given list of signed 64-bit integer [values].
  int writeListUint64(List<int> values) {
    _ensureNoVTable();
    _prepare(_sizeofUint64, values.length, additionalBytes: _sizeofUint32);
    final int result = _tail;
    int tail = _tail;
    _setUint32AtTail(_buf, tail, values.length);
    tail -= _sizeofUint32;
    for (int value in values) {
      _setUint64AtTail(_buf, tail, value);
      tail -= _sizeofUint64;
    }
    return result;
  }

  /// Write the given list of signed 32-bit integer [values].
  int writeListInt32(List<int> values) {
    _ensureNoVTable();
    _prepare(_sizeofUint32, 1 + values.length);
    final int result = _tail;
    int tail = _tail;
    _setUint32AtTail(_buf, tail, values.length);
    tail -= _sizeofUint32;
    for (int value in values) {
      _setInt32AtTail(_buf, tail, value);
      tail -= _sizeofInt32;
    }
    return result;
  }

  /// Write the given list of unsigned 32-bit integer [values].
  int writeListUint32(List<int> values) {
    _ensureNoVTable();
    _prepare(_sizeofUint32, 1 + values.length);
    final int result = _tail;
    int tail = _tail;
    _setUint32AtTail(_buf, tail, values.length);
    tail -= _sizeofUint32;
    for (int value in values) {
      _setUint32AtTail(_buf, tail, value);
      tail -= _sizeofUint32;
    }
    return result;
  }

  /// Write the given list of signed 16-bit integer [values].
  int writeListInt16(List<int> values) {
    _ensureNoVTable();
    _prepare(_sizeofUint32, 1, additionalBytes: 2 * values.length);
    final int result = _tail;
    int tail = _tail;
    _setUint32AtTail(_buf, tail, values.length);
    tail -= _sizeofUint32;
    for (int value in values) {
      _setInt16AtTail(_buf, tail, value);
      tail -= _sizeofInt16;
    }
    return result;
  }

  /// Write the given list of unsigned 16-bit integer [values].
  int writeListUint16(List<int> values) {
    _ensureNoVTable();
    _prepare(_sizeofUint32, 1, additionalBytes: 2 * values.length);
    final int result = _tail;
    int tail = _tail;
    _setUint32AtTail(_buf, tail, values.length);
    tail -= _sizeofUint32;
    for (int value in values) {
      _setUint16AtTail(_buf, tail, value);
      tail -= _sizeofUint16;
    }
    return result;
  }

  /// Write the given list of bools as unsigend 8-bit integer [values].
  int writeListBool(List<bool> values) {
    return writeListUint8(values?.map((b) => b ? 1 : 0)?.toList());
  }

  /// Write the given list of signed 8-bit integer [values].
  int writeListInt8(List<int> values) {
    _ensureNoVTable();
    _prepare(_sizeofUint32, 1, additionalBytes: values.length);
    final int result = _tail;
    int tail = _tail;
    _setUint32AtTail(_buf, tail, values.length);
    tail -= _sizeofUint32;
    for (int value in values) {
      _setInt8AtTail(_buf, tail, value);
      tail -= _sizeofUint8;
    }
    return result;
  }

  /// Write the given list of unsigned 8-bit integer [values].
  int writeListUint8(List<int> values) {
    _ensureNoVTable();
    _prepare(_sizeofUint32, 1, additionalBytes: values.length);
    final int result = _tail;
    int tail = _tail;
    _setUint32AtTail(_buf, tail, values.length);
    tail -= _sizeofUint32;
    for (int value in values) {
      _setUint8AtTail(_buf, tail, value);
      tail -= _sizeofUint8;
    }
    return result;
  }

  /// Write the given string [value] and return its offset, or `null` if
  /// the [value] is `null`.
  int writeString(String value) {
    _ensureNoVTable();
    if (value != null) {
      if (_strings != null) {
        return _strings.putIfAbsent(value, () => _writeString(value));
      } else {
        return _writeString(value);
      }
    }
    return null;
  }

  int _writeString(String value) {
    // TODO(scheglov) optimize for ASCII strings
    List<int> bytes = utf8.encode(value);
    int length = bytes.length;
    _prepare(4, 1, additionalBytes: length + 1);
    final int result = _tail;
    _setUint32AtTail(_buf, _tail, length);
    int offset = _buf.lengthInBytes - _tail + 4;
    for (int i = 0; i < length; i++) {
      _buf.setUint8(offset++, bytes[i]);
    }
    _buf.setUint8(offset, 0); // trailing zero
    return result;
  }

  /// Throw an exception if there is not currently a vtable.
  void _ensureCurrentVTable() {
    if (_currentVTable == null) {
      throw new StateError('Start a table before adding values.');
    }
  }

  /// Throw an exception if there is currently a vtable.
  void _ensureNoVTable() {
    if (_currentVTable != null) {
      throw new StateError(
          'Cannot write a non-scalar value while writing a table.');
    }
  }

  /// The number of bytes that have been written to the buffer so far.  The
  /// most recently written byte is this many bytes from the end of the buffer.
  int get offset => _tail;

  /// Zero-pads the buffer, which may be required for some struct layouts.
  void pad(int howManyBytes) {
    for (int i = 0; i < howManyBytes; i++) putUint8(0);
  }

  /// Prepare for writing the given `count` of scalars of the given `size`.
  /// Additionally allocate the specified `additionalBytes`. Update the current
  /// tail pointer to point at the allocated space.
  void _prepare(int size, int count, {int additionalBytes = 0}) {
    // Update the alignment.
    if (_maxAlign < size) {
      _maxAlign = size;
    }
    // Prepare amount of required space.
    int dataSize = size * count + additionalBytes;
    int alignDelta = (-(_tail + dataSize)) % size;
    int bufSize = alignDelta + dataSize;
    // Ensure that we have the required amount of space.
    {
      int oldCapacity = _buf.lengthInBytes;
      if (_tail + bufSize > oldCapacity) {
        int desiredNewCapacity = (oldCapacity + bufSize) * 2;
        int deltaCapacity = desiredNewCapacity - oldCapacity;
        deltaCapacity += (-deltaCapacity) % _maxAlign;
        int newCapacity = oldCapacity + deltaCapacity;
        _buf = _allocator.resize(_buf, newCapacity, oldCapacity, 0);
      }
    }
    // Update the tail pointer.
    _tail += bufSize;
  }

  /// Record the offset of the given [field].
  void _trackField(int field) {
    _currentVTable.addField(field, _tail);
  }

  static void _setFloat64AtTail(ByteData _buf, int tail, double x) {
    _buf.setFloat64(_buf.lengthInBytes - tail, x, Endian.little);
  }

  static void _setFloat32AtTail(ByteData _buf, int tail, double x) {
    _buf.setFloat32(_buf.lengthInBytes - tail, x, Endian.little);
  }

  static void _setUint64AtTail(ByteData _buf, int tail, int x) {
    _buf.setUint64(_buf.lengthInBytes - tail, x, Endian.little);
  }

  static void _setInt64AtTail(ByteData _buf, int tail, int x) {
    _buf.setInt64(_buf.lengthInBytes - tail, x, Endian.little);
  }

  static void _setInt32AtTail(ByteData _buf, int tail, int x) {
    _buf.setInt32(_buf.lengthInBytes - tail, x, Endian.little);
  }

  static void _setUint32AtTail(ByteData _buf, int tail, int x) {
    _buf.setUint32(_buf.lengthInBytes - tail, x, Endian.little);
  }

  static void _setInt16AtTail(ByteData _buf, int tail, int x) {
    _buf.setInt16(_buf.lengthInBytes - tail, x, Endian.little);
  }

  static void _setUint16AtTail(ByteData _buf, int tail, int x) {
    _buf.setUint16(_buf.lengthInBytes - tail, x, Endian.little);
  }

  static void _setInt8AtTail(ByteData _buf, int tail, int x) {
    _buf.setInt8(_buf.lengthInBytes - tail, x);
  }

  static void _setUint8AtTail(ByteData _buf, int tail, int x) {
    _buf.setUint8(_buf.lengthInBytes - tail, x);
  }
}

/// Reader of lists of boolean values.
///
/// The returned unmodifiable lists lazily read values on access.
class BoolListReader extends Reader<List<bool>> {
  const BoolListReader();

  @override
  int get size => _sizeofUint32;

  @override
  List<bool> read(BufferContext bc, int offset) =>
      new _FbBoolList(bc, bc.derefObject(offset));
}

/// The reader of booleans.
class BoolReader extends Reader<bool> {
  const BoolReader() : super();

  @override
  int get size => _sizeofUint8;

  @override
  bool read(BufferContext bc, int offset) => bc._getInt8(offset) != 0;
}

/// The reader of lists of 64-bit float values.
///
/// The returned unmodifiable lists lazily read values on access.
class Float64ListReader extends Reader<List<double>> {
  const Float64ListReader();

  @override
  int get size => _sizeofFloat64;

  @override
  List<double> read(BufferContext bc, int offset) =>
      new _FbFloat64List(bc, bc.derefObject(offset));
}

class Float32ListReader extends Reader<List<double>> {
  const Float32ListReader();

  @override
  int get size => _sizeofFloat32;

  @override
  List<double> read(BufferContext bc, int offset) =>
      new _FbFloat32List(bc, bc.derefObject(offset));
}

class Float64Reader extends Reader<double> {
  const Float64Reader();

  @override
  int get size => _sizeofFloat64;

  @override
  double read(BufferContext bc, int offset) => bc._getFloat64(offset);
}

class Float32Reader extends Reader<double> {
  const Float32Reader();

  @override
  int get size => _sizeofFloat32;

  @override
  double read(BufferContext bc, int offset) => bc._getFloat32(offset);
}

class Int64Reader extends Reader<int> {
  const Int64Reader() : super();
  @override
  int get size => _sizeofInt64;

  @override
  int read(BufferContext bc, int offset) => bc._getInt64(offset);
}

/// The reader of signed 32-bit integers.
class Int32Reader extends Reader<int> {
  const Int32Reader() : super();

  @override
  int get size => _sizeofInt32;

  @override
  int read(BufferContext bc, int offset) => bc._getInt32(offset);
}

/// The reader of signed 32-bit integers.
class Int16Reader extends Reader<int> {
  const Int16Reader() : super();

  @override
  int get size => _sizeofInt16;

  @override
  int read(BufferContext bc, int offset) => bc._getInt16(offset);
}

/// The reader of 8-bit signed integers.
class Int8Reader extends Reader<int> {
  const Int8Reader() : super();

  @override
  int get size => _sizeofInt8;

  @override
  int read(BufferContext bc, int offset) => bc._getInt8(offset);
}

/// The reader of lists of objects.
///
/// The returned unmodifiable lists lazily read objects on access.
class ListReader<E> extends Reader<List<E>> {
  final Reader<E> _elementReader;

  const ListReader(this._elementReader);

  @override
  int get size => _sizeofUint32;

  @override
  List<E> read(BufferContext bc, int offset) =>
      new _FbGenericList<E>(_elementReader, bc, bc.derefObject(offset));
}

/// Object that can read a value at a [BufferContext].
abstract class Reader<T> {
  const Reader();

  /// The size of the value in bytes.
  int get size;

  /// Read the value at the given [offset] in [bc].
  T read(BufferContext bc, int offset);

  /// Read the value of the given [field] in the given [object].
  T vTableGet(BufferContext object, int offset, int field, [T defaultValue]) {
    int vTableSOffset = object._getInt32(offset);
    int vTableOffset = offset - vTableSOffset;
    int vTableSize = object._getUint16(vTableOffset);
    int vTableFieldOffset = field;
    if (vTableFieldOffset < vTableSize) {
      int fieldOffsetInObject =
          object._getUint16(vTableOffset + vTableFieldOffset);
      if (fieldOffsetInObject != 0) {
        return read(object, offset + fieldOffsetInObject);
      }
    }
    return defaultValue;
  }
}

/// The reader of string values.
class StringReader extends Reader<String> {
  const StringReader() : super();

  @override
  int get size => 4;

  @override
  String read(BufferContext bc, int offset) {
    int strOffset = bc.derefObject(offset);
    int length = bc._getUint32(strOffset);
    Uint8List bytes = bc._asUint8LIst(strOffset + 4, length);
    if (_isLatin(bytes)) {
      return new String.fromCharCodes(bytes);
    }
    return utf8.decode(bytes);
  }

  static bool _isLatin(Uint8List bytes) {
    int length = bytes.length;
    for (int i = 0; i < length; i++) {
      if (bytes[i] > 127) {
        return false;
      }
    }
    return true;
  }
}

/// An abstract reader for structs.
abstract class StructReader<T> extends Reader<T> {
  const StructReader();

  /// Return the object at `offset`.
  T createObject(BufferContext bc, int offset);

  T read(BufferContext bp, int offset) {
    return createObject(bp, offset);
  }
}

/// An abstract reader for tables.
abstract class TableReader<T> extends Reader<T> {
  const TableReader();

  @override
  int get size => 4;

  /// Return the object at [offset].
  T createObject(BufferContext bc, int offset);

  @override
  T read(BufferContext bp, int offset) {
    int objectOffset = bp.derefObject(offset);
    return createObject(bp, objectOffset);
  }
}

/// Reader of lists of unsigned 32-bit integer values.
///
/// The returned unmodifiable lists lazily read values on access.
class Uint32ListReader extends Reader<List<int>> {
  const Uint32ListReader();

  @override
  int get size => _sizeofUint32;

  @override
  List<int> read(BufferContext bc, int offset) =>
      new _FbUint32List(bc, bc.derefObject(offset));
}

/// The reader of unsigned 64-bit integers.
///
/// WARNING: May have compatibility issues with JavaScript
class Uint64Reader extends Reader<int> {
  const Uint64Reader() : super();

  @override
  int get size => _sizeofUint64;

  @override
  int read(BufferContext bc, int offset) => bc._getUint64(offset);
}

/// The reader of unsigned 32-bit integers.
class Uint32Reader extends Reader<int> {
  const Uint32Reader() : super();

  @override
  int get size => _sizeofUint32;

  @override
  int read(BufferContext bc, int offset) => bc._getUint32(offset);
}

/// Reader of lists of unsigned 32-bit integer values.
///
/// The returned unmodifiable lists lazily read values on access.
class Uint16ListReader extends Reader<List<int>> {
  const Uint16ListReader();

  @override
  int get size => _sizeofUint32;

  @override
  List<int> read(BufferContext bc, int offset) =>
      new _FbUint16List(bc, bc.derefObject(offset));
}

/// The reader of unsigned 32-bit integers.
class Uint16Reader extends Reader<int> {
  const Uint16Reader() : super();

  @override
  int get size => _sizeofUint16;

  @override
  int read(BufferContext bc, int offset) => bc._getUint16(offset);
}

/// Reader of lists of unsigned 8-bit integer values.
///
/// The returned unmodifiable lists lazily read values on access.
class Uint8ListReader extends Reader<List<int>> {
  const Uint8ListReader();

  @override
  int get size => _sizeofUint32;

  @override
  List<int> read(BufferContext bc, int offset) =>
      new _FbUint8List(bc, bc.derefObject(offset));
}

/// The reader of unsigned 8-bit integers.
class Uint8Reader extends Reader<int> {
  const Uint8Reader() : super();

  @override
  int get size => _sizeofUint8;

  @override
  int read(BufferContext bc, int offset) => bc._getUint8(offset);
}

/// The list backed by 64-bit values - Uint64 length and Float64.
class _FbFloat64List extends _FbList<double> {
  _FbFloat64List(BufferContext bc, int offset) : super(bc, offset);

  @override
  double operator [](int i) {
    return bc._getFloat64(offset + 4 + 8 * i);
  }
}

/// The list backed by 32-bit values - Float32.
class _FbFloat32List extends _FbList<double> {
  _FbFloat32List(BufferContext bc, int offset) : super(bc, offset);

  @override
  double operator [](int i) {
    return bc._getFloat32(offset + 4 + 4 * i);
  }
}

/// List backed by a generic object which may have any size.
class _FbGenericList<E> extends _FbList<E> {
  final Reader<E> elementReader;

  List<E> _items;

  _FbGenericList(this.elementReader, BufferContext bp, int offset)
      : super(bp, offset);

  @override
  E operator [](int i) {
    _items ??= new List<E>(length);
    E item = _items[i];
    if (item == null) {
      item = elementReader.read(bc, offset + 4 + elementReader.size * i);
      _items[i] = item;
    }
    return item;
  }
}

/// The base class for immutable lists read from flat buffers.
abstract class _FbList<E> extends Object with ListMixin<E> implements List<E> {
  final BufferContext bc;
  final int offset;
  int _length;

  _FbList(this.bc, this.offset);

  @override
  int get length {
    _length ??= bc._getUint32(offset);
    return _length;
  }

  @override
  void set length(int i) =>
      throw new StateError('Attempt to modify immutable list');

  @override
  void operator []=(int i, E e) =>
      throw new StateError('Attempt to modify immutable list');
}

/// List backed by 32-bit unsigned integers.
class _FbUint32List extends _FbList<int> {
  _FbUint32List(BufferContext bc, int offset) : super(bc, offset);

  @override
  int operator [](int i) {
    return bc._getUint32(offset + 4 + 4 * i);
  }
}

/// List backed by 16-bit unsigned integers.
class _FbUint16List extends _FbList<int> {
  _FbUint16List(BufferContext bc, int offset) : super(bc, offset);

  @override
  int operator [](int i) {
    return bc._getUint16(offset + 4 + 2 * i);
  }
}

/// List backed by 8-bit unsigned integers.
class _FbUint8List extends _FbList<int> {
  _FbUint8List(BufferContext bc, int offset) : super(bc, offset);

  @override
  int operator [](int i) {
    return bc._getUint8(offset + 4 + i);
  }
}

/// List backed by 8-bit unsigned integers.
class _FbBoolList extends _FbList<bool> {
  _FbBoolList(BufferContext bc, int offset) : super(bc, offset);

  @override
  bool operator [](int i) {
    return bc._getUint8(offset + 4 + i) == 1 ? true : false;
  }
}

/// Class that describes the structure of a table.
class _VTable {
  static const int _metadataLength = 4;

  final List<int> fieldTails = <int>[];
  final List<int> fieldOffsets = <int>[];

  /// The size of the table that uses this VTable.
  int tableSize;

  /// The tail of this VTable.  It is used to share the same VTable between
  /// multiple tables of identical structure.
  int tail;

  int get _vTableSize => numOfUint16 * _sizeofUint16;

  int get numOfUint16 => 1 + 1 + fieldTails.length;

  void addField(int field, int offset) {
    while (fieldTails.length <= field) {
      fieldTails.add(null);
    }
    fieldTails[field] = offset;
  }

  bool _offsetsMatch(int vt2Start, ByteData buf) {
    for (int i = 0; i < fieldOffsets.length; i++) {
      if (fieldOffsets[i] !=
          buf.getUint16(
              vt2Start + _metadataLength + (2 * i), Endian.little)) {
        return false;
      }
    }
    return true;
  }

  /// Fill the [fieldOffsets] field.
  void computeFieldOffsets(int tableTail) {
    assert(fieldOffsets.isEmpty);
    for (int fieldTail in fieldTails) {
      int fieldOffset = fieldTail == null ? 0 : tableTail - fieldTail;
      fieldOffsets.add(fieldOffset);
    }
  }

  /// Outputs this VTable to [buf], which is is expected to be aligned to 16-bit
  /// and have at least [numOfUint16] 16-bit words available.
  void output(ByteData buf, int bufOffset) {
    // VTable size.
    buf.setUint16(bufOffset, numOfUint16 * 2, Endian.little);
    bufOffset += 2;
    // Table size.
    buf.setUint16(bufOffset, tableSize, Endian.little);
    bufOffset += 2;
    // Field offsets.
    for (int fieldOffset in fieldOffsets) {
      buf.setUint16(bufOffset, fieldOffset, Endian.little);
      bufOffset += 2;
    }
  }
}

/// The interface that [Builder] uses to allocate buffers for encoding.
abstract class Allocator {
  const Allocator();

  /// Allocate a [ByteData] buffer of a given size.
  ByteData allocate(int size);

  /// Free the given [ByteData] buffer previously allocated by [allocate].
  void deallocate(ByteData data);

  /// Reallocate [newSize] bytes of memory, replacing the old [oldData]. This
  /// grows downwards, and is intended specifically for use with [Builder].
  /// Params [inUseBack] and [inUseFront] indicate how much of [oldData] is
  /// actually in use at each end, and needs to be copied.
  ByteData resize(
      ByteData oldData, int newSize, int inUseBack, int inUseFront) {
    final newData = allocate(newSize);
    clear(newData, true);
    _copyDownward(oldData, newData, inUseBack, inUseFront);
    deallocate(oldData);
    return newData;
  }

  /// Clear the allocated data contents.
  ///
  /// Param [isFresh] is true if the given data has been freshly allocated,
  /// depending on the allocator implementation, clearing may be unnecessary.
  void clear(ByteData data, bool isFresh) {
    final length = data.lengthInBytes;
    final length64b = (length / 8).floor();
    // fillRange iterates over data so it's faster with larger data type
    if (length64b > 0) data.buffer.asUint64List().fillRange(0, length64b, 0);
    data.buffer.asUint8List().fillRange(length64b * 8, length % 8, 0);
  }

  /// Called by [resize] to copy memory from [oldData] to [newData]. Only
  /// memory of size [inUseFront] and [inUseBack] will be copied from the front
  /// and back of the old memory allocation.
  void _copyDownward(
      ByteData oldData, ByteData newData, int inUseBack, int inUseFront) {
    if (inUseBack != 0) {
      newData.buffer.asUint8List().setAll(
          newData.lengthInBytes - inUseBack,
          oldData.buffer.asUint8List().getRange(
              oldData.lengthInBytes - inUseBack, oldData.lengthInBytes));
    }
    if (inUseFront != 0) {
      newData.buffer
          .asUint8List()
          .setAll(0, oldData.buffer.asUint8List().getRange(0, inUseFront));
    }
  }
}

class DefaultAllocator extends Allocator {
  const DefaultAllocator();

  @override
  ByteData allocate(int size) => ByteData(size);

  @override
  void deallocate(ByteData _) {
    // nothing to do, it's garbage-collected
  }

  @override
  void clear(ByteData data, bool isFresh) {
    if (isFresh) {
      // nothing to do, ByteData is created all zeroed out
    } else {
      super.clear(data, isFresh);
    }
  }
}

const _defaultAllocator = DefaultAllocator();
