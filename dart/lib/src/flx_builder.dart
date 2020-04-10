import 'dart:convert';
import 'dart:typed_data';

import 'flx_types.dart';

/// The main builder class for creation of a FlexBuffer
class FlxBuilder {
  ByteData _buffer;
  List<_StackValue> _stack;
  List<_StackPointer> _stackPointers;
  int _offset;
  bool _finished;
  Map<String, _StackValue> _stringCache;
  Map<String, _StackValue> _keyCache;
  Map<_KeysHash, _StackValue> _keyVectorCache;
  Map<int, _StackValue> _indirectIntCache;
  Map<double, _StackValue> _indirectDoubleCache;

  /// Instantiate the builder if you intent to gradually build up the buffer by calling
  /// add... methods and calling finish() to receive the the resulting byte array.
  /// The default size of internal buffer is set to 2048. Provide a different value in order to avoid buffer copies.
  FlxBuilder([int size = 2048]) {
    _buffer = ByteData(size);
    _stack = [];
    _stackPointers = [];
    _offset = 0;
    _finished = false;
    _stringCache = {};
    _keyCache = {};
    _keyVectorCache = {};
    _indirectIntCache = {};
    _indirectDoubleCache = {};
  }

  /// Use this method in order to turn an object into a FlexBuffer directly.
  /// Please use the manual instantiation of the [FlxBuilder] and gradual addition of values, if performance is more important than convenience.
  static ByteBuffer buildFromObject(dynamic value) {
    var flx = FlxBuilder();
    flx._add(value);
    var buffer = flx.finish();
    var bd = ByteData(buffer.lengthInBytes);
    bd.buffer.asUint8List().setAll(0, buffer);
    return bd.buffer;
  }

  void _add(dynamic value) {
    if (value == null) {
      addNull();
    } else if (value is bool) {
      addBool(value);
    } else if (value is int) {
      addInt(value);
    } else if (value is double) {
      addDouble(value);
    } else if (value is ByteBuffer) {
      addBlob(value);
    } else if (value is String) {
      addString(value);
    } else if (value is List<dynamic>) {
      startVector();
      for (var i = 0; i < value.length; i++) {
        _add(value[i]);
      }
      end();
    } else if (value is Map<String, dynamic>) {
      startMap();
      value.forEach((key, value) {
        addKey(key);
        _add(value);
      });
      end();
    } else {
      throw Exception('Value of unexpected type: ${value}');
    }
  }

  void addNull() {
    _integrityCheckOnValueAddition();
    _stack.add(_StackValue.WithNull());
  }
  void addInt(int value) {
    _integrityCheckOnValueAddition();
    _stack.add(_StackValue.WithInt(value));
  }
  void addBool(bool value) {
    _integrityCheckOnValueAddition();
    _stack.add(_StackValue.WithBool(value));
  }
  void addDouble(double value) {
    _integrityCheckOnValueAddition();
    _stack.add(_StackValue.WithDouble(value));
  }

  void addString(String value) {
    _integrityCheckOnValueAddition();
    if(_stringCache.containsKey(value)) {
      _stack.add(_stringCache[value]);
      return;
    }
    var utf8String = utf8.encode(value);
    var length = utf8String.length;
    var bitWidth = BitWidthUtil.width(length);
    var byteWidth = _align(bitWidth);
    _writeInt(length, byteWidth);
    var stringOffset = _offset;
    var newOffset = _newOffset(length + 1);
    _pushBuffer(utf8String);
    _offset = newOffset;
    var stackValue = _StackValue.WithOffset(stringOffset, ValueType.String, bitWidth);
    _stack.add(stackValue);
    _stringCache[value] = stackValue;
  }

  /// This methods adds a key to a map and should be followed by an add... value call.
  /// It also implies that you call this method only after you called [startMap].
  void addKey(String value) {
    _integrityCheckOnKeyAddition();
    if(_keyCache.containsKey(value)) {
      _stack.add(_keyCache[value]);
      return;
    }
    var utf8String = utf8.encode(value);
    var length = utf8String.length;
    var keyOffset = _offset;
    var newOffset = _newOffset(length + 1);
    _pushBuffer(utf8String);
    _offset = newOffset;
    var stackValue = _StackValue.WithOffset(keyOffset, ValueType.Key, BitWidth.width8);
    _stack.add(stackValue);
    _keyCache[value] = stackValue;
  }

  void addBlob(ByteBuffer value) {
    _integrityCheckOnValueAddition();
    var length = value.lengthInBytes;
    var bitWidth = BitWidthUtil.width(length);
    var byteWidth = _align(bitWidth);
    _writeInt(length, byteWidth);
    var blobOffset = _offset;
    var newOffset = _newOffset(length);
    _pushBuffer(value.asUint8List());
    _offset = newOffset;
    var stackValue = _StackValue.WithOffset(blobOffset, ValueType.Blob, bitWidth);
    _stack.add(stackValue);
  }

  /// Adding large integer values indirectly might be beneficial if those values suppose to be store in a vector together with small integer values.
  /// This is due to the fact that FlexBuffers will add padding to small integer values, if they are stored together with large integer values.
  /// When we add integer indirectly the vector of ints will contain not the value itself, but only the relative offset to the value.
  /// By setting the [cache] parameter to true, you make sure that the builder tracks added int value and performs deduplication.
  void addIntIndirectly(int value, [bool cache = false]) {
    _integrityCheckOnValueAddition();
    if (_indirectIntCache.containsKey(value)) {
      _stack.add(_indirectIntCache[value]);
      return;
    }
    var stackValue = _StackValue.WithInt(value);
    var byteWidth = _align(stackValue.width);
    var newOffset = _newOffset(byteWidth);
    var valueOffset = _offset;
    _pushBuffer(stackValue.asU8List(stackValue.width));
    var stackOffset = _StackValue.WithOffset(valueOffset, ValueType.IndirectInt, stackValue.width);
    _stack.add(stackOffset);
    _offset = newOffset;
    if(cache) {
      _indirectIntCache[value] = stackOffset;
    }
  }

  /// Double are stored as 8 or 4 byte values in FlexBuffers. If they are stored in a mixed vector, values which are smaller than 4 / 8 bytes will be padded.
  /// When we add double indirectly, the vector will contain not the value itself, but only the relative offset to the value. Which could occupy only 1 or 2 bytes, reducing the odds for unnecessary padding.
  /// By setting the [cache] parameter to true, you make sure that the builder tracks already added double value and performs deduplication.
  void addDoubleIndirectly(double value, [bool cache = false]) {
    _integrityCheckOnValueAddition();
    if (cache && _indirectDoubleCache.containsKey(value)) {
      _stack.add(_indirectDoubleCache[value]);
      return;
    }
    var stackValue = _StackValue.WithDouble(value);
    var byteWidth = _align(stackValue.width);
    var newOffset = _newOffset(byteWidth);
    var valueOffset = _offset;
    _pushBuffer(stackValue.asU8List(stackValue.width));
    var stackOffset = _StackValue.WithOffset(valueOffset, ValueType.IndirectFloat, stackValue.width);
    _stack.add(stackOffset);
    _offset = newOffset;
    if(cache) {
      _indirectDoubleCache[value] = stackOffset;
    }
  }

  /// This method starts a vector definition and needs to be followed by 0 to n add... value calls.
  /// The vector definition needs to be finished with an [end] call.
  /// It is also possible to add nested vector or map by calling [startVector] / [startMap].
  void startVector() {
    _integrityCheckOnValueAddition();
    _stackPointers.add(_StackPointer(_stack.length, true));
  }

  /// This method starts a map definition and needs to be followed by 0 to n [addKey] +  add... value calls.
  /// The map definition needs to be finished with an [end] call.
  /// It is also possible to add nested vector or map by calling [startVector] / [startMap] after calling [addKey].
  void startMap() {
    _integrityCheckOnValueAddition();
    _stackPointers.add(_StackPointer(_stack.length, false));
  }

  /// Marks that the addition of values to the last vector, or map have ended.
  void end() {
    var pointer = _stackPointers.removeLast();
    if (pointer.isVector) {
      _endVector(pointer);
    } else {
      _sortKeysAndEndMap(pointer);
    }
  }

  /// Finish building the FlatBuffer and return array of bytes.
  /// Can be called multiple times, to get the array of bytes.
  /// After the first call, adding values, or starting vectors / maps will result in an exception.
  Uint8List finish() {
    if (_finished == false) {
      _finish();
    }
    return _buffer.buffer.asUint8List(0, _offset);
  }
  
  void _integrityCheckOnValueAddition() {
    if(_finished) {
      throw Exception('Adding values after finish is prohibited');
    }
    if(_stackPointers.isNotEmpty && _stackPointers.last.isVector == false) {
      if (_stack.last.type != ValueType.Key) {
        throw Exception('Adding value to a map before adding a key is prohibited');
      }
    }
  }

  void _integrityCheckOnKeyAddition() {
    if(_finished) {
      throw Exception('Adding values after finish is prohibited');
    }
    if(_stackPointers.isEmpty || _stackPointers.last.isVector) {
      throw Exception('Adding key before staring a map is prohibited');
    }
  }

  void _finish() {
    if (_stack.length != 1) {
      throw Exception('Stack has to be exactly 1');
    }
    var value = _stack[0];
    var byteWidth = _align(value.elementWidth(_offset, 0));
    _writeStackValue(value, byteWidth);
    _writeInt(value.storedPackedType(), 1);
    _writeInt(byteWidth, 1);
    _finished = true;
  }
  
  _StackValue _createVector(int start, int vecLength, int step, [_StackValue keys]) {
    var bitWidth = BitWidthUtil.width(vecLength);
    var prefixElements = 1;
    if (keys != null) {
      var elemWidth = keys.elementWidth(_offset, 0);
      if (elemWidth.index > bitWidth.index) {
        bitWidth = elemWidth;
      }
      prefixElements += 2;
    }
    var vectorType = ValueType.Key;
    var typed = keys == null;
    for (var i = start; i < _stack.length; i+=step) {
      var elemWidth = _stack[i].elementWidth(_offset, i + prefixElements);
      if (elemWidth.index > bitWidth.index) {
        bitWidth = elemWidth;
      }
      if (i == start) {
        vectorType = _stack[i].type;
        typed &= vectorType.isTypedVectorElement();
      } else {
        if (vectorType != _stack[i].type) {
          typed = false;
        }
      }
    }
    var byteWidth = _align(bitWidth);
    var fix = typed & vectorType.isNumber() && vecLength >= 2 && vecLength <= 4;
    if (keys != null) {
      _writeStackValue(keys, byteWidth);
      _writeInt(1 << keys.width.index, byteWidth);
    }
    if (fix == false) {
      _writeInt(vecLength, byteWidth);
    }
    var vecOffset = _offset;
    for (var i = start; i < _stack.length; i+=step) {
      _writeStackValue(_stack[i], byteWidth);
    }
    if (typed == false) {
      for (var i = start; i < _stack.length; i+=step) {
        _writeInt(_stack[i].storedPackedType(), 1);
      }
    }
    if (keys != null) {
      return _StackValue.WithOffset(vecOffset, ValueType.Map, bitWidth);
    }
    if(typed) {
      var vType = vectorType.toTypedVector(fix ? vecLength : 0);
      return _StackValue.WithOffset(vecOffset, vType, bitWidth);
    }
    return _StackValue.WithOffset(vecOffset, ValueType.Vector, bitWidth);
  }

  void _endVector(_StackPointer pointer) {
    var vecLength = _stack.length - pointer.stackPosition;
    var vec = _createVector(pointer.stackPosition, vecLength, 1);
    _stack.removeRange(pointer.stackPosition, _stack.length);
    _stack.add(vec);
  }

  void _sortKeysAndEndMap(_StackPointer pointer) {
    if (((_stack.length - pointer.stackPosition) & 1) == 1) {
      throw Exception('The stack needs to hold key value pairs (even number of elements)');
    }

    var sorted = true;
    for (var i = pointer.stackPosition; i < _stack.length - 2; i+=2) {
      if (_shouldFlip(_stack[i], _stack[i+2])) {
        sorted = false;
        break;
      }
    }

    if (sorted == false) {
      for (var i = pointer.stackPosition; i < _stack.length; i+=2) {
        var flipIndex = i;
        for (var j = i + 2; j < _stack.length; j+=2) {
          if (_shouldFlip(_stack[flipIndex], _stack[j])) {
            flipIndex = j;
          }
        }
        if (flipIndex != i) {
          var k = _stack[flipIndex];
          var v = _stack[flipIndex + 1];
          _stack[flipIndex] = _stack[i];
          _stack[flipIndex + 1] = _stack[i + 1];
          _stack[i] = k;
          _stack[i + 1] = v;
        }
      }
    }
    _endMap(pointer);
  }
  
  void _endMap(_StackPointer pointer) {
    var vecLength = (_stack.length - pointer.stackPosition) >> 1;
    var offsets = <int>[];
    for (var i = pointer.stackPosition; i < _stack.length; i += 2) {
      offsets.add(_stack[i].offset);
    }
    var keysHash = _KeysHash(offsets);
    var keysStackValue;
    if (_keyVectorCache.containsKey(keysHash)) {
      keysStackValue = _keyVectorCache[keysHash];
    } else {
      keysStackValue = _createVector(pointer.stackPosition, vecLength, 2);
      _keyVectorCache[keysHash] = keysStackValue;
    }
    var vec = _createVector(pointer.stackPosition + 1, vecLength, 2, keysStackValue);
    _stack.removeRange(pointer.stackPosition, _stack.length);
    _stack.add(vec);
  }

  bool _shouldFlip(_StackValue v1, _StackValue v2) {
    if (v1.type != ValueType.Key || v2.type != ValueType.Key) {
      throw Exception('Stack values are not keys ${v1} | ${v2}');
    }

    var c1, c2;
    var index = 0;
    do {
      c1 = _buffer.getUint8(v1.offset + index);
      c2 = _buffer.getUint8(v2.offset + index);
      if (c2 < c1) return true;
      if (c1 < c2) return false;
      index += 1;
    } while (c1 !=0 && c2 != 0);
    return false;
  }

  int _align(BitWidth width) {
    var byteWidth = width.toByteWidth();
    _offset += BitWidthUtil.paddingSize(_offset, byteWidth);
    return byteWidth;
  }

  void _writeStackValue(_StackValue value, int byteWidth) {
    var newOffset = _newOffset(byteWidth);
    if (value.isOffset) {
      var relativeOffset = _offset - value.offset;
      if (byteWidth == 8 || relativeOffset < (1 << (byteWidth * 8))) {
        _writeInt(relativeOffset, byteWidth);
      } else {
        throw Exception('Unexpected size');
      }
    } else {
      _pushBuffer(value.asU8List(BitWidthUtil.fromByteWidth(byteWidth)));
    }
    _offset = newOffset;
  }

  void _writeInt(int value, int byteWidth) {
    var newOffset = _newOffset(byteWidth);
    _pushInt(value, BitWidthUtil.fromByteWidth(byteWidth));
    _offset = newOffset;
  }

  int _newOffset(int newValueSize) {
    var newOffset = _offset + newValueSize;
    var size = _buffer.lengthInBytes;
    var prevSize = size;
    while (size < newOffset) {
      size <<= 1;
    }
    if (prevSize < size) {
      var newBuf = ByteData(size);
      newBuf.buffer
          .asUint8List()
          .setAll(0, _buffer.buffer.asUint8List());
    }
    return newOffset;
  }

  void _pushInt(int value, BitWidth width) {
    switch (width) {

      case BitWidth.width8:
        _buffer.setInt8(_offset, value);
        break;
      case BitWidth.width16:
        _buffer.setInt16(_offset, value, Endian.little);
        break;
      case BitWidth.width32:
        _buffer.setInt32(_offset, value, Endian.little);
        break;
      case BitWidth.width64:
        _buffer.setInt64(_offset, value, Endian.little);
        break;
    }
  }

  void _pushBuffer(List<int> value) {
    _buffer.buffer.asUint8List().setAll(_offset, value);
  }
}

class _StackValue {
  dynamic _value;
  int _offset;
  ValueType _type;
  BitWidth _width;
  _StackValue.WithNull() {
    _type = ValueType.Null;
    _width = BitWidth.width8;
  }
  _StackValue.WithInt(int value) {
    _type = value != null ? ValueType.Int : ValueType.Null;
    _width = BitWidthUtil.width(value);
    _value = value;
  }
  _StackValue.WithBool(bool value) {
    _type = value != null ? ValueType.Bool : ValueType.Null;
    _width = BitWidth.width8;
    _value = value;
  }
  _StackValue.WithDouble(double value) {
    _type = value != null ? ValueType.Float : ValueType.Null;
    _width = BitWidthUtil.width(value);
    _value = value;
  }
  _StackValue.WithOffset(int value, ValueType type, BitWidth width) {
    _offset = value;
    _type = type;
    _width = width;
  }

  BitWidth storedWidth([BitWidth width = BitWidth.width8]) {
    return _type.isInline() ? _width.max(width) : _width;
  }

  int storedPackedType([BitWidth width = BitWidth.width8]) {
    return _type.packedType(storedWidth(width));
  }

  BitWidth elementWidth(int size, int index) {
    if (_type.isInline()) return _width;
    for(var i = 0; i < 4; i++) {
      var width = 1 << i;
      var offsetLoc = size + BitWidthUtil.paddingSize(size, width) + index * width;
      var offset = offsetLoc - _offset;
      var bitWidth = BitWidthUtil.width(offset);
      if (1 << bitWidth.index == width) {
        return bitWidth;
      }
    }
    throw Exception('Element is of unknown width');
  }

  List<int> asU8List(BitWidth width) {
    if (_type.isNumber()) {
      if(_type == ValueType.Float) {
        if(width == BitWidth.width32) {
          var result = ByteData(4);
          result.setFloat32(0, _value, Endian.little);
          return result.buffer.asUint8List();
        } else {
          var result = ByteData(8);
          result.setFloat64(0, _value, Endian.little);
          return result.buffer.asUint8List();
        }
      } else {
        switch(width) {
          case BitWidth.width8:
            var result = ByteData(1);
            result.setInt8(0, _value);
            return result.buffer.asUint8List();
          case BitWidth.width16:
            var result = ByteData(2);
            result.setInt16(0, _value, Endian.little);
            return result.buffer.asUint8List();
          case BitWidth.width32:
            var result = ByteData(4);
            result.setInt32(0, _value, Endian.little);
            return result.buffer.asUint8List();
          case BitWidth.width64:
            var result = ByteData(8);
            result.setInt64(0, _value, Endian.little);
            return result.buffer.asUint8List();
        }
      }
    }
    if(_type == ValueType.Null) {
      var result = ByteData(1);
      result.setInt8(0, 0);
      return result.buffer.asUint8List();
    }
    if(_type == ValueType.Bool) {
      var result = ByteData(1);
      result.setInt8(0, _value ? 1 : 0);
      return result.buffer.asUint8List();
    }

    throw Exception('Unexpected type');
  }

  ValueType get type {
    return _type;
  }

  BitWidth get width {
    return _width;
  }

  bool get isOffset {
    return !_type.isInline();
  }
  int get offset => _offset;

  bool get isF32 {
    return _type == ValueType.Float && _width == BitWidth.width32;
  }
}

class _StackPointer {
  int stackPosition;
  bool isVector;
  _StackPointer(this.stackPosition, this.isVector);
}

class _KeysHash {
  List<int> keys;

  _KeysHash(this.keys);

  @override
  bool operator ==(Object other) {
    if (other is _KeysHash) {
      if (keys.length != other.keys.length) return false;
      for (var i = 0; i < keys.length; i++) {
        if (keys[i] != other.keys[i]) return false;
      }
      return true;
    }
    return false;
  }

  @override
  int get hashCode {
    var result = 17;
    for (var i = 0; i < keys.length; i++) {
      result = result * 23 + keys[i];
    }
    return result;
  }
}
