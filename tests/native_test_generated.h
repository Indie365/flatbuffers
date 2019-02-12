// automatically generated by the FlatBuffers compiler, do not modify


#ifndef FLATBUFFERS_GENERATED_NATIVETEST_H_
#define FLATBUFFERS_GENERATED_NATIVETEST_H_

#include "flatbuffers/flatbuffers.h"

struct Complex;

struct Comp;

struct Mat;

struct Foo;

inline const flatbuffers::TypeTable *ComplexTypeTable();

inline const flatbuffers::TypeTable *CompTypeTable();

inline const flatbuffers::TypeTable *MatTypeTable();

inline const flatbuffers::TypeTable *FooTypeTable();

enum BundleSize {
  BundleSize_Size2 = 0,
  BundleSize_Size3 = 1,
  BundleSize_Size6 = 2,
  BundleSize_MIN = BundleSize_Size2,
  BundleSize_MAX = BundleSize_Size6
};

inline const BundleSize (&EnumValuesBundleSize())[3] {
  static const BundleSize values[] = {
    BundleSize_Size2,
    BundleSize_Size3,
    BundleSize_Size6
  };
  return values;
}

inline const char * const *EnumNamesBundleSize() {
  static const char * const names[] = {
    "Size2",
    "Size3",
    "Size6",
    nullptr
  };
  return names;
}

inline const char *EnumNameBundleSize(BundleSize e) {
  if (e < BundleSize_Size2 || e > BundleSize_Size6) return "";
  const size_t index = static_cast<int>(e);
  return EnumNamesBundleSize()[index];
}

FLATBUFFERS_MANUALLY_ALIGNED_STRUCT(8) Complex FLATBUFFERS_FINAL_CLASS {
 private:
  double i_;
  double q_;

 public:
  Complex() {
    memset(this, 0, sizeof(Complex));
  }
  Complex(double _i, double _q)
      : i_(flatbuffers::EndianScalar(_i)),
        q_(flatbuffers::EndianScalar(_q)) {
  }
  double i() const {
    return flatbuffers::EndianScalar(i_);
  }
  double q() const {
    return flatbuffers::EndianScalar(q_);
  }
};
FLATBUFFERS_STRUCT_END(Complex, 16);

inline bool operator==(const Complex &lhs, const Complex &rhs) {
  return
      (lhs.i() == rhs.i()) &&
      (lhs.q() == rhs.q());
}

FLATBUFFERS_MANUALLY_ALIGNED_STRUCT(8) Comp FLATBUFFERS_FINAL_CLASS {
 private:
  double i_;
  double q_;

 public:
  Comp() {
    memset(this, 0, sizeof(Comp));
  }
  Comp(double _i, double _q)
      : i_(flatbuffers::EndianScalar(_i)),
        q_(flatbuffers::EndianScalar(_q)) {
  }
  double i() const {
    return flatbuffers::EndianScalar(i_);
  }
  double q() const {
    return flatbuffers::EndianScalar(q_);
  }
};
FLATBUFFERS_STRUCT_END(Comp, 16);

inline bool operator==(const Comp &lhs, const Comp &rhs) {
  return
      (lhs.i() == rhs.i()) &&
      (lhs.q() == rhs.q());
}

struct Mat FLATBUFFERS_FINAL_CLASS : private flatbuffers::Table {
  static const flatbuffers::TypeTable *MiniReflectTypeTable() {
    return MatTypeTable();
  }
  enum FlatBuffersVTableOffset FLATBUFFERS_VTABLE_UNDERLYING_TYPE {
    VT_ROWS = 4,
    VT_DATA = 6
  };
  int32_t rows() const {
    return GetField<int32_t>(VT_ROWS, 0);
  }
  const flatbuffers::Vector<const Complex *> *data() const {
    return GetPointer<const flatbuffers::Vector<const Complex *> *>(VT_DATA);
  }
  bool Verify(flatbuffers::Verifier &verifier) const {
    return VerifyTableStart(verifier) &&
           VerifyField<int32_t>(verifier, VT_ROWS) &&
           VerifyOffset(verifier, VT_DATA) &&
           verifier.VerifyVector(data()) &&
           verifier.EndTable();
  }
};

struct MatBuilder {
  flatbuffers::FlatBufferBuilder &fbb_;
  flatbuffers::uoffset_t start_;
  void add_rows(int32_t rows) {
    fbb_.AddElement<int32_t>(Mat::VT_ROWS, rows, 0);
  }
  void add_data(flatbuffers::Offset<flatbuffers::Vector<const Complex *>> data) {
    fbb_.AddOffset(Mat::VT_DATA, data);
  }
  explicit MatBuilder(flatbuffers::FlatBufferBuilder &_fbb)
        : fbb_(_fbb) {
    start_ = fbb_.StartTable();
  }
  MatBuilder &operator=(const MatBuilder &);
  flatbuffers::Offset<Mat> Finish() {
    const auto end = fbb_.EndTable(start_);
    auto o = flatbuffers::Offset<Mat>(end);
    return o;
  }
};

inline flatbuffers::Offset<Mat> CreateMat(
    flatbuffers::FlatBufferBuilder &_fbb,
    int32_t rows = 0,
    flatbuffers::Offset<flatbuffers::Vector<const Complex *>> data = 0) {
  MatBuilder builder_(_fbb);
  builder_.add_data(data);
  builder_.add_rows(rows);
  return builder_.Finish();
}

inline flatbuffers::Offset<Mat> CreateMatDirect(
    flatbuffers::FlatBufferBuilder &_fbb,
    int32_t rows = 0,
    const std::vector<Complex> *data = nullptr) {
  auto data__ = data ? _fbb.CreateVectorOfStructs<Complex>(*data) : 0;
  return CreateMat(
      _fbb,
      rows,
      data__);
}

struct Foo FLATBUFFERS_FINAL_CLASS : private flatbuffers::Table {
  static const flatbuffers::TypeTable *MiniReflectTypeTable() {
    return FooTypeTable();
  }
  enum FlatBuffersVTableOffset FLATBUFFERS_VTABLE_UNDERLYING_TYPE {
    VT_ENUMDATA = 4,
    VT_BITDATA = 6,
    VT_IQDATA = 8,
    VT_IQSAMPLE = 10,
    VT_IQSAMPLE2 = 12,
    VT_NEWINT = 14
  };
  BundleSize enumData() const {
    return static_cast<BundleSize>(GetField<int8_t>(VT_ENUMDATA, 0));
  }
  const Mat *bitData() const {
    return GetPointer<const Mat *>(VT_BITDATA);
  }
  const flatbuffers::Vector<const Complex *> *iqData() const {
    return GetPointer<const flatbuffers::Vector<const Complex *> *>(VT_IQDATA);
  }
  const Complex *iqSample() const {
    return GetStruct<const Complex *>(VT_IQSAMPLE);
  }
  const Comp *iqSample2() const {
    return GetStruct<const Comp *>(VT_IQSAMPLE2);
  }
  int32_t newInt() const {
    return GetField<int32_t>(VT_NEWINT, 0);
  }
  bool Verify(flatbuffers::Verifier &verifier) const {
    return VerifyTableStart(verifier) &&
           VerifyField<int8_t>(verifier, VT_ENUMDATA) &&
           VerifyOffset(verifier, VT_BITDATA) &&
           verifier.VerifyTable(bitData()) &&
           VerifyOffset(verifier, VT_IQDATA) &&
           verifier.VerifyVector(iqData()) &&
           VerifyField<Complex>(verifier, VT_IQSAMPLE) &&
           VerifyField<Comp>(verifier, VT_IQSAMPLE2) &&
           VerifyField<int32_t>(verifier, VT_NEWINT) &&
           verifier.EndTable();
  }
};

struct FooBuilder {
  flatbuffers::FlatBufferBuilder &fbb_;
  flatbuffers::uoffset_t start_;
  void add_enumData(BundleSize enumData) {
    fbb_.AddElement<int8_t>(Foo::VT_ENUMDATA, static_cast<int8_t>(enumData), 0);
  }
  void add_bitData(flatbuffers::Offset<Mat> bitData) {
    fbb_.AddOffset(Foo::VT_BITDATA, bitData);
  }
  void add_iqData(flatbuffers::Offset<flatbuffers::Vector<const Complex *>> iqData) {
    fbb_.AddOffset(Foo::VT_IQDATA, iqData);
  }
  void add_iqSample(const Complex *iqSample) {
    fbb_.AddStruct(Foo::VT_IQSAMPLE, iqSample);
  }
  void add_iqSample2(const Comp *iqSample2) {
    fbb_.AddStruct(Foo::VT_IQSAMPLE2, iqSample2);
  }
  void add_newInt(int32_t newInt) {
    fbb_.AddElement<int32_t>(Foo::VT_NEWINT, newInt, 0);
  }
  explicit FooBuilder(flatbuffers::FlatBufferBuilder &_fbb)
        : fbb_(_fbb) {
    start_ = fbb_.StartTable();
  }
  FooBuilder &operator=(const FooBuilder &);
  flatbuffers::Offset<Foo> Finish() {
    const auto end = fbb_.EndTable(start_);
    auto o = flatbuffers::Offset<Foo>(end);
    return o;
  }
};

inline flatbuffers::Offset<Foo> CreateFoo(
    flatbuffers::FlatBufferBuilder &_fbb,
    BundleSize enumData = BundleSize_Size2,
    flatbuffers::Offset<Mat> bitData = 0,
    flatbuffers::Offset<flatbuffers::Vector<const Complex *>> iqData = 0,
    const Complex *iqSample = 0,
    const Comp *iqSample2 = 0,
    int32_t newInt = 0) {
  FooBuilder builder_(_fbb);
  builder_.add_newInt(newInt);
  builder_.add_iqSample2(iqSample2);
  builder_.add_iqSample(iqSample);
  builder_.add_iqData(iqData);
  builder_.add_bitData(bitData);
  builder_.add_enumData(enumData);
  return builder_.Finish();
}

inline flatbuffers::Offset<Foo> CreateFooDirect(
    flatbuffers::FlatBufferBuilder &_fbb,
    BundleSize enumData = BundleSize_Size2,
    flatbuffers::Offset<Mat> bitData = 0,
    const std::vector<Complex> *iqData = nullptr,
    const Complex *iqSample = 0,
    const Comp *iqSample2 = 0,
    int32_t newInt = 0) {
  auto iqData__ = iqData ? _fbb.CreateVectorOfStructs<Complex>(*iqData) : 0;
  return CreateFoo(
      _fbb,
      enumData,
      bitData,
      iqData__,
      iqSample,
      iqSample2,
      newInt);
}

inline const flatbuffers::TypeTable *BundleSizeTypeTable() {
  static const flatbuffers::TypeCode type_codes[] = {
    { flatbuffers::ET_CHAR, 0, 0 },
    { flatbuffers::ET_CHAR, 0, 0 },
    { flatbuffers::ET_CHAR, 0, 0 }
  };
  static const flatbuffers::TypeFunction type_refs[] = {
    BundleSizeTypeTable
  };
  static const char * const names[] = {
    "Size2",
    "Size3",
    "Size6"
  };
  static const flatbuffers::TypeTable tt = {
    flatbuffers::ST_ENUM, 3, type_codes, type_refs, nullptr, names
  };
  return &tt;
}

inline const flatbuffers::TypeTable *ComplexTypeTable() {
  static const flatbuffers::TypeCode type_codes[] = {
    { flatbuffers::ET_DOUBLE, 0, -1 },
    { flatbuffers::ET_DOUBLE, 0, -1 }
  };
  static const int64_t values[] = { 0, 8, 16 };
  static const char * const names[] = {
    "i",
    "q"
  };
  static const flatbuffers::TypeTable tt = {
    flatbuffers::ST_STRUCT, 2, type_codes, nullptr, values, names
  };
  return &tt;
}

inline const flatbuffers::TypeTable *CompTypeTable() {
  static const flatbuffers::TypeCode type_codes[] = {
    { flatbuffers::ET_DOUBLE, 0, -1 },
    { flatbuffers::ET_DOUBLE, 0, -1 }
  };
  static const int64_t values[] = { 0, 8, 16 };
  static const char * const names[] = {
    "i",
    "q"
  };
  static const flatbuffers::TypeTable tt = {
    flatbuffers::ST_STRUCT, 2, type_codes, nullptr, values, names
  };
  return &tt;
}

inline const flatbuffers::TypeTable *MatTypeTable() {
  static const flatbuffers::TypeCode type_codes[] = {
    { flatbuffers::ET_INT, 0, -1 },
    { flatbuffers::ET_SEQUENCE, 1, 0 }
  };
  static const flatbuffers::TypeFunction type_refs[] = {
    ComplexTypeTable
  };
  static const char * const names[] = {
    "rows",
    "data"
  };
  static const flatbuffers::TypeTable tt = {
    flatbuffers::ST_TABLE, 2, type_codes, type_refs, nullptr, names
  };
  return &tt;
}

inline const flatbuffers::TypeTable *FooTypeTable() {
  static const flatbuffers::TypeCode type_codes[] = {
    { flatbuffers::ET_CHAR, 0, 0 },
    { flatbuffers::ET_SEQUENCE, 0, 1 },
    { flatbuffers::ET_SEQUENCE, 1, 2 },
    { flatbuffers::ET_SEQUENCE, 0, 2 },
    { flatbuffers::ET_SEQUENCE, 0, 3 },
    { flatbuffers::ET_INT, 0, -1 }
  };
  static const flatbuffers::TypeFunction type_refs[] = {
    BundleSizeTypeTable,
    MatTypeTable,
    ComplexTypeTable,
    CompTypeTable
  };
  static const char * const names[] = {
    "enumData",
    "bitData",
    "iqData",
    "iqSample",
    "iqSample2",
    "newInt"
  };
  static const flatbuffers::TypeTable tt = {
    flatbuffers::ST_TABLE, 6, type_codes, type_refs, nullptr, names
  };
  return &tt;
}

inline const Foo *GetFoo(const void *buf) {
  return flatbuffers::GetRoot<Foo>(buf);
}

inline const Foo *GetSizePrefixedFoo(const void *buf) {
  return flatbuffers::GetSizePrefixedRoot<Foo>(buf);
}

inline bool VerifyFooBuffer(
    flatbuffers::Verifier &verifier) {
  return verifier.VerifyBuffer<Foo>(nullptr);
}

inline bool VerifySizePrefixedFooBuffer(
    flatbuffers::Verifier &verifier) {
  return verifier.VerifySizePrefixedBuffer<Foo>(nullptr);
}

inline void FinishFooBuffer(
    flatbuffers::FlatBufferBuilder &fbb,
    flatbuffers::Offset<Foo> root) {
  fbb.Finish(root);
}

inline void FinishSizePrefixedFooBuffer(
    flatbuffers::FlatBufferBuilder &fbb,
    flatbuffers::Offset<Foo> root) {
  fbb.FinishSizePrefixed(root);
}

#endif  // FLATBUFFERS_GENERATED_NATIVETEST_H_
