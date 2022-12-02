// automatically generated by the FlatBuffers compiler, do not modify


#ifndef FLATBUFFERS_GENERATED_KEYFIELDSAMPLE_KEYFIELD_SAMPLE_H_
#define FLATBUFFERS_GENERATED_KEYFIELDSAMPLE_KEYFIELD_SAMPLE_H_

#include "flatbuffers/flatbuffers.h"

// Ensure the included flatbuffers.h is the same version as when this file was
// generated, otherwise it may not be compatible.
static_assert(FLATBUFFERS_VERSION_MAJOR == 22 &&
              FLATBUFFERS_VERSION_MINOR == 11 &&
              FLATBUFFERS_VERSION_REVISION == 23,
             "Non-compatible flatbuffers version included");

namespace keyfield {
namespace sample {

struct Baz;

struct Bar;

struct FooTable;
struct FooTableBuilder;
struct FooTableT;

bool operator==(const Baz &lhs, const Baz &rhs);
bool operator!=(const Baz &lhs, const Baz &rhs);
bool operator==(const Bar &lhs, const Bar &rhs);
bool operator!=(const Bar &lhs, const Bar &rhs);
bool operator==(const FooTableT &lhs, const FooTableT &rhs);
bool operator!=(const FooTableT &lhs, const FooTableT &rhs);

inline const flatbuffers::TypeTable *BazTypeTable();

inline const flatbuffers::TypeTable *BarTypeTable();

inline const flatbuffers::TypeTable *FooTableTypeTable();

FLATBUFFERS_MANUALLY_ALIGNED_STRUCT(1) Baz FLATBUFFERS_FINAL_CLASS {
 private:
  uint8_t a_[4];
  uint8_t b_;

 public:
  static const flatbuffers::TypeTable *MiniReflectTypeTable() {
    return BazTypeTable();
  }
  Baz()
      : a_(),
        b_(0) {
  }
  Baz(uint8_t _b)
      : a_(),
        b_(flatbuffers::EndianScalar(_b)) {
  }
  Baz(flatbuffers::span<const uint8_t, 4> _a, uint8_t _b)
      : b_(flatbuffers::EndianScalar(_b)) {
    flatbuffers::CastToArray(a_).CopyFromSpan(_a);
  }
  const flatbuffers::Array<uint8_t, 4> *a() const {
    return &flatbuffers::CastToArray(a_);
  }
  flatbuffers::Array<uint8_t, 4> *mutable_a() {
    return &flatbuffers::CastToArray(a_);
  }
  bool KeyCompareLessThan(const Baz * const o) const {
    return KeyCompareWithValue(o->a()) < 0;
  }
  int KeyCompareWithValue(const flatbuffers::Array<uint8_t, 4> *_a) const {
    for (auto i = 0; i < a()->size(); i++) {
      const auto a_l = flatbuffers::EndianScalar(a_[i]);
      const auto a_r = _a->Get(i);
      if(a_l != a_r)
        return static_cast<int>(a_l > a_r) - static_cast<int>(a_l < a_r);
    }
    return 0;
  }
  uint8_t b() const {
    return flatbuffers::EndianScalar(b_);
  }
  void mutate_b(uint8_t _b) {
    flatbuffers::WriteScalar(&b_, _b);
  }
};
FLATBUFFERS_STRUCT_END(Baz, 5);

inline bool operator==(const Baz &lhs, const Baz &rhs) {
  return
      (lhs.a() == rhs.a()) &&
      (lhs.b() == rhs.b());
}

inline bool operator!=(const Baz &lhs, const Baz &rhs) {
    return !(lhs == rhs);
}


FLATBUFFERS_MANUALLY_ALIGNED_STRUCT(4) Bar FLATBUFFERS_FINAL_CLASS {
 private:
  float a_[3];
  uint8_t b_;
  int8_t padding0__;  int16_t padding1__;

 public:
  static const flatbuffers::TypeTable *MiniReflectTypeTable() {
    return BarTypeTable();
  }
  Bar()
      : a_(),
        b_(0),
        padding0__(0),
        padding1__(0) {
    (void)padding0__;
    (void)padding1__;
  }
  Bar(uint8_t _b)
      : a_(),
        b_(flatbuffers::EndianScalar(_b)),
        padding0__(0),
        padding1__(0) {
    (void)padding0__;
    (void)padding1__;
  }
  Bar(flatbuffers::span<const float, 3> _a, uint8_t _b)
      : b_(flatbuffers::EndianScalar(_b)),
        padding0__(0),
        padding1__(0) {
    flatbuffers::CastToArray(a_).CopyFromSpan(_a);
    (void)padding0__;
    (void)padding1__;
  }
  const flatbuffers::Array<float, 3> *a() const {
    return &flatbuffers::CastToArray(a_);
  }
  flatbuffers::Array<float, 3> *mutable_a() {
    return &flatbuffers::CastToArray(a_);
  }
  bool KeyCompareLessThan(const Bar * const o) const {
    return KeyCompareWithValue(o->a()) < 0;
  }
  int KeyCompareWithValue(const flatbuffers::Array<float, 3> *_a) const {
    for (auto i = 0; i < a()->size(); i++) {
      const auto a_l = a_[i];
      const auto a_r = flatbuffers::EndianScalar(_a->Get(i));
      if(a_l != a_r)
        return static_cast<int>(a_l > a_r) - static_cast<int>(a_l < a_r);
    }
    return 0;
  }
  uint8_t b() const {
    return flatbuffers::EndianScalar(b_);
  }
  void mutate_b(uint8_t _b) {
    flatbuffers::WriteScalar(&b_, _b);
  }
};
FLATBUFFERS_STRUCT_END(Bar, 16);

inline bool operator==(const Bar &lhs, const Bar &rhs) {
  return
      (lhs.a() == rhs.a()) &&
      (lhs.b() == rhs.b());
}

inline bool operator!=(const Bar &lhs, const Bar &rhs) {
    return !(lhs == rhs);
}


struct FooTableT : public flatbuffers::NativeTable {
  typedef FooTable TableType;
  int32_t a = 0;
  int32_t b = 0;
  std::string c{};
  std::vector<keyfield::sample::Baz> d{};
  std::vector<keyfield::sample::Bar> e{};
};

struct FooTable FLATBUFFERS_FINAL_CLASS : private flatbuffers::Table {
  typedef FooTableT NativeTableType;
  typedef FooTableBuilder Builder;
  static const flatbuffers::TypeTable *MiniReflectTypeTable() {
    return FooTableTypeTable();
  }
  enum FlatBuffersVTableOffset FLATBUFFERS_VTABLE_UNDERLYING_TYPE {
    VT_A = 4,
    VT_B = 6,
    VT_C = 8,
    VT_D = 10,
    VT_E = 12
  };
  int32_t a() const {
    return GetField<int32_t>(VT_A, 0);
  }
  bool mutate_a(int32_t _a = 0) {
    return SetField<int32_t>(VT_A, _a, 0);
  }
  int32_t b() const {
    return GetField<int32_t>(VT_B, 0);
  }
  bool mutate_b(int32_t _b = 0) {
    return SetField<int32_t>(VT_B, _b, 0);
  }
  const flatbuffers::String *c() const {
    return GetPointer<const flatbuffers::String *>(VT_C);
  }
  flatbuffers::String *mutable_c() {
    return GetPointer<flatbuffers::String *>(VT_C);
  }
  bool KeyCompareLessThan(const FooTable * const o) const {
    return *c() < *o->c();
  }
  int KeyCompareWithValue(const char *_c) const {
    return strcmp(c()->c_str(), _c);
  }
  const flatbuffers::Vector<const keyfield::sample::Baz *> *d() const {
    return GetPointer<const flatbuffers::Vector<const keyfield::sample::Baz *> *>(VT_D);
  }
  flatbuffers::Vector<const keyfield::sample::Baz *> *mutable_d() {
    return GetPointer<flatbuffers::Vector<const keyfield::sample::Baz *> *>(VT_D);
  }
  const flatbuffers::Vector<const keyfield::sample::Bar *> *e() const {
    return GetPointer<const flatbuffers::Vector<const keyfield::sample::Bar *> *>(VT_E);
  }
  flatbuffers::Vector<const keyfield::sample::Bar *> *mutable_e() {
    return GetPointer<flatbuffers::Vector<const keyfield::sample::Bar *> *>(VT_E);
  }
  bool Verify(flatbuffers::Verifier &verifier) const {
    return VerifyTableStart(verifier) &&
           VerifyField<int32_t>(verifier, VT_A, 4) &&
           VerifyField<int32_t>(verifier, VT_B, 4) &&
           VerifyOffsetRequired(verifier, VT_C) &&
           verifier.VerifyString(c()) &&
           VerifyOffset(verifier, VT_D) &&
           verifier.VerifyVector(d()) &&
           VerifyOffset(verifier, VT_E) &&
           verifier.VerifyVector(e()) &&
           verifier.EndTable();
  }
  FooTableT *UnPack(const flatbuffers::resolver_function_t *_resolver = nullptr) const;
  void UnPackTo(FooTableT *_o, const flatbuffers::resolver_function_t *_resolver = nullptr) const;
  static flatbuffers::Offset<FooTable> Pack(flatbuffers::FlatBufferBuilder &_fbb, const FooTableT* _o, const flatbuffers::rehasher_function_t *_rehasher = nullptr);
};

struct FooTableBuilder {
  typedef FooTable Table;
  flatbuffers::FlatBufferBuilder &fbb_;
  flatbuffers::uoffset_t start_;
  void add_a(int32_t a) {
    fbb_.AddElement<int32_t>(FooTable::VT_A, a, 0);
  }
  void add_b(int32_t b) {
    fbb_.AddElement<int32_t>(FooTable::VT_B, b, 0);
  }
  void add_c(flatbuffers::Offset<flatbuffers::String> c) {
    fbb_.AddOffset(FooTable::VT_C, c);
  }
  void add_d(flatbuffers::Offset<flatbuffers::Vector<const keyfield::sample::Baz *>> d) {
    fbb_.AddOffset(FooTable::VT_D, d);
  }
  void add_e(flatbuffers::Offset<flatbuffers::Vector<const keyfield::sample::Bar *>> e) {
    fbb_.AddOffset(FooTable::VT_E, e);
  }
  explicit FooTableBuilder(flatbuffers::FlatBufferBuilder &_fbb)
        : fbb_(_fbb) {
    start_ = fbb_.StartTable();
  }
  flatbuffers::Offset<FooTable> Finish() {
    const auto end = fbb_.EndTable(start_);
    auto o = flatbuffers::Offset<FooTable>(end);
    fbb_.Required(o, FooTable::VT_C);
    return o;
  }
};

inline flatbuffers::Offset<FooTable> CreateFooTable(
    flatbuffers::FlatBufferBuilder &_fbb,
    int32_t a = 0,
    int32_t b = 0,
    flatbuffers::Offset<flatbuffers::String> c = 0,
    flatbuffers::Offset<flatbuffers::Vector<const keyfield::sample::Baz *>> d = 0,
    flatbuffers::Offset<flatbuffers::Vector<const keyfield::sample::Bar *>> e = 0) {
  FooTableBuilder builder_(_fbb);
  builder_.add_e(e);
  builder_.add_d(d);
  builder_.add_c(c);
  builder_.add_b(b);
  builder_.add_a(a);
  return builder_.Finish();
}

inline flatbuffers::Offset<FooTable> CreateFooTableDirect(
    flatbuffers::FlatBufferBuilder &_fbb,
    int32_t a = 0,
    int32_t b = 0,
    const char *c = nullptr,
    std::vector<keyfield::sample::Baz> *d = nullptr,
    std::vector<keyfield::sample::Bar> *e = nullptr) {
  auto c__ = c ? _fbb.CreateString(c) : 0;
  auto d__ = d ? _fbb.CreateVectorOfSortedStructs<keyfield::sample::Baz>(d) : 0;
  auto e__ = e ? _fbb.CreateVectorOfSortedStructs<keyfield::sample::Bar>(e) : 0;
  return keyfield::sample::CreateFooTable(
      _fbb,
      a,
      b,
      c__,
      d__,
      e__);
}

flatbuffers::Offset<FooTable> CreateFooTable(flatbuffers::FlatBufferBuilder &_fbb, const FooTableT *_o, const flatbuffers::rehasher_function_t *_rehasher = nullptr);


inline bool operator==(const FooTableT &lhs, const FooTableT &rhs) {
  return
      (lhs.a == rhs.a) &&
      (lhs.b == rhs.b) &&
      (lhs.c == rhs.c) &&
      (lhs.d == rhs.d) &&
      (lhs.e == rhs.e);
}

inline bool operator!=(const FooTableT &lhs, const FooTableT &rhs) {
    return !(lhs == rhs);
}


inline FooTableT *FooTable::UnPack(const flatbuffers::resolver_function_t *_resolver) const {
  auto _o = std::unique_ptr<FooTableT>(new FooTableT());
  UnPackTo(_o.get(), _resolver);
  return _o.release();
}

inline void FooTable::UnPackTo(FooTableT *_o, const flatbuffers::resolver_function_t *_resolver) const {
  (void)_o;
  (void)_resolver;
  { auto _e = a(); _o->a = _e; }
  { auto _e = b(); _o->b = _e; }
  { auto _e = c(); if (_e) _o->c = _e->str(); }
  { auto _e = d(); if (_e) { _o->d.resize(_e->size()); for (flatbuffers::uoffset_t _i = 0; _i < _e->size(); _i++) { _o->d[_i] = *_e->Get(_i); } } else { _o->d.resize(0); } }
  { auto _e = e(); if (_e) { _o->e.resize(_e->size()); for (flatbuffers::uoffset_t _i = 0; _i < _e->size(); _i++) { _o->e[_i] = *_e->Get(_i); } } else { _o->e.resize(0); } }
}

inline flatbuffers::Offset<FooTable> FooTable::Pack(flatbuffers::FlatBufferBuilder &_fbb, const FooTableT* _o, const flatbuffers::rehasher_function_t *_rehasher) {
  return CreateFooTable(_fbb, _o, _rehasher);
}

inline flatbuffers::Offset<FooTable> CreateFooTable(flatbuffers::FlatBufferBuilder &_fbb, const FooTableT *_o, const flatbuffers::rehasher_function_t *_rehasher) {
  (void)_rehasher;
  (void)_o;
  struct _VectorArgs { flatbuffers::FlatBufferBuilder *__fbb; const FooTableT* __o; const flatbuffers::rehasher_function_t *__rehasher; } _va = { &_fbb, _o, _rehasher}; (void)_va;
  auto _a = _o->a;
  auto _b = _o->b;
  auto _c = _fbb.CreateString(_o->c);
  auto _d = _o->d.size() ? _fbb.CreateVectorOfStructs(_o->d) : 0;
  auto _e = _o->e.size() ? _fbb.CreateVectorOfStructs(_o->e) : 0;
  return keyfield::sample::CreateFooTable(
      _fbb,
      _a,
      _b,
      _c,
      _d,
      _e);
}

inline const flatbuffers::TypeTable *BazTypeTable() {
  static const flatbuffers::TypeCode type_codes[] = {
    { flatbuffers::ET_UCHAR, 1, -1 },
    { flatbuffers::ET_UCHAR, 0, -1 }
  };
  static const int16_t array_sizes[] = { 4,  };
  static const int64_t values[] = { 0, 4, 5 };
  static const char * const names[] = {
    "a",
    "b"
  };
  static const flatbuffers::TypeTable tt = {
    flatbuffers::ST_STRUCT, 2, type_codes, nullptr, array_sizes, values, names
  };
  return &tt;
}

inline const flatbuffers::TypeTable *BarTypeTable() {
  static const flatbuffers::TypeCode type_codes[] = {
    { flatbuffers::ET_FLOAT, 1, -1 },
    { flatbuffers::ET_UCHAR, 0, -1 }
  };
  static const int16_t array_sizes[] = { 3,  };
  static const int64_t values[] = { 0, 12, 16 };
  static const char * const names[] = {
    "a",
    "b"
  };
  static const flatbuffers::TypeTable tt = {
    flatbuffers::ST_STRUCT, 2, type_codes, nullptr, array_sizes, values, names
  };
  return &tt;
}

inline const flatbuffers::TypeTable *FooTableTypeTable() {
  static const flatbuffers::TypeCode type_codes[] = {
    { flatbuffers::ET_INT, 0, -1 },
    { flatbuffers::ET_INT, 0, -1 },
    { flatbuffers::ET_STRING, 0, -1 },
    { flatbuffers::ET_SEQUENCE, 1, 0 },
    { flatbuffers::ET_SEQUENCE, 1, 1 }
  };
  static const flatbuffers::TypeFunction type_refs[] = {
    keyfield::sample::BazTypeTable,
    keyfield::sample::BarTypeTable
  };
  static const char * const names[] = {
    "a",
    "b",
    "c",
    "d",
    "e"
  };
  static const flatbuffers::TypeTable tt = {
    flatbuffers::ST_TABLE, 5, type_codes, type_refs, nullptr, nullptr, names
  };
  return &tt;
}

inline const keyfield::sample::FooTable *GetFooTable(const void *buf) {
  return flatbuffers::GetRoot<keyfield::sample::FooTable>(buf);
}

inline const keyfield::sample::FooTable *GetSizePrefixedFooTable(const void *buf) {
  return flatbuffers::GetSizePrefixedRoot<keyfield::sample::FooTable>(buf);
}

inline FooTable *GetMutableFooTable(void *buf) {
  return flatbuffers::GetMutableRoot<FooTable>(buf);
}

inline keyfield::sample::FooTable *GetMutableSizePrefixedFooTable(void *buf) {
  return flatbuffers::GetMutableSizePrefixedRoot<keyfield::sample::FooTable>(buf);
}

inline bool VerifyFooTableBuffer(
    flatbuffers::Verifier &verifier) {
  return verifier.VerifyBuffer<keyfield::sample::FooTable>(nullptr);
}

inline bool VerifySizePrefixedFooTableBuffer(
    flatbuffers::Verifier &verifier) {
  return verifier.VerifySizePrefixedBuffer<keyfield::sample::FooTable>(nullptr);
}

inline void FinishFooTableBuffer(
    flatbuffers::FlatBufferBuilder &fbb,
    flatbuffers::Offset<keyfield::sample::FooTable> root) {
  fbb.Finish(root);
}

inline void FinishSizePrefixedFooTableBuffer(
    flatbuffers::FlatBufferBuilder &fbb,
    flatbuffers::Offset<keyfield::sample::FooTable> root) {
  fbb.FinishSizePrefixed(root);
}

inline flatbuffers::unique_ptr<keyfield::sample::FooTableT> UnPackFooTable(
    const void *buf,
    const flatbuffers::resolver_function_t *res = nullptr) {
  return flatbuffers::unique_ptr<keyfield::sample::FooTableT>(GetFooTable(buf)->UnPack(res));
}

inline flatbuffers::unique_ptr<keyfield::sample::FooTableT> UnPackSizePrefixedFooTable(
    const void *buf,
    const flatbuffers::resolver_function_t *res = nullptr) {
  return flatbuffers::unique_ptr<keyfield::sample::FooTableT>(GetSizePrefixedFooTable(buf)->UnPack(res));
}

}  // namespace sample
}  // namespace keyfield

#endif  // FLATBUFFERS_GENERATED_KEYFIELDSAMPLE_KEYFIELD_SAMPLE_H_
