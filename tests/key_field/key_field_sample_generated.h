// automatically generated by the FlatBuffers compiler, do not modify


#ifndef FLATBUFFERS_GENERATED_KEYFIELDSAMPLE_KEYFIELD_SAMPLE_H_
#define FLATBUFFERS_GENERATED_KEYFIELDSAMPLE_KEYFIELD_SAMPLE_H_

#include "flatbuffers/flatbuffers.h"

// Ensure the included flatbuffers.h is the same version as when this file was
// generated, otherwise it may not be compatible.
static_assert(FLATBUFFERS_VERSION_MAJOR == 23 &&
              FLATBUFFERS_VERSION_MINOR == 1 &&
              FLATBUFFERS_VERSION_REVISION == 4,
             "Non-compatible flatbuffers version included");

namespace keyfield {
namespace sample {

struct Baz;

struct Bar;

struct Color;

struct Apple;

struct Fruit;

struct Rice;

struct Grain;

struct FooTable;
struct FooTableBuilder;
struct FooTableT;

bool operator==(const Baz &lhs, const Baz &rhs);
bool operator!=(const Baz &lhs, const Baz &rhs);
bool operator==(const Bar &lhs, const Bar &rhs);
bool operator!=(const Bar &lhs, const Bar &rhs);
bool operator==(const Color &lhs, const Color &rhs);
bool operator!=(const Color &lhs, const Color &rhs);
bool operator==(const Apple &lhs, const Apple &rhs);
bool operator!=(const Apple &lhs, const Apple &rhs);
bool operator==(const Fruit &lhs, const Fruit &rhs);
bool operator!=(const Fruit &lhs, const Fruit &rhs);
bool operator==(const Rice &lhs, const Rice &rhs);
bool operator!=(const Rice &lhs, const Rice &rhs);
bool operator==(const Grain &lhs, const Grain &rhs);
bool operator!=(const Grain &lhs, const Grain &rhs);
bool operator==(const FooTableT &lhs, const FooTableT &rhs);
bool operator!=(const FooTableT &lhs, const FooTableT &rhs);

inline const ::flatbuffers::TypeTable *BazTypeTable();

inline const ::flatbuffers::TypeTable *BarTypeTable();

inline const ::flatbuffers::TypeTable *ColorTypeTable();

inline const ::flatbuffers::TypeTable *AppleTypeTable();

inline const ::flatbuffers::TypeTable *FruitTypeTable();

inline const ::flatbuffers::TypeTable *RiceTypeTable();

inline const ::flatbuffers::TypeTable *GrainTypeTable();

inline const ::flatbuffers::TypeTable *FooTableTypeTable();

FLATBUFFERS_MANUALLY_ALIGNED_STRUCT(1) Baz FLATBUFFERS_FINAL_CLASS {
 private:
  uint8_t a_[4];
  uint8_t b_;

 public:
  static const ::flatbuffers::TypeTable *MiniReflectTypeTable() {
    return BazTypeTable();
  }
  Baz()
      : a_(),
        b_(0) {
  }
  Baz(uint8_t _b)
      : a_(),
        b_(::flatbuffers::EndianScalar(_b)) {
  }
  Baz(::flatbuffers::span<const uint8_t, 4> _a, uint8_t _b)
      : b_(::flatbuffers::EndianScalar(_b)) {
    ::flatbuffers::CastToArray(a_).CopyFromSpan(_a);
  }
  const ::flatbuffers::Array<uint8_t, 4> *a() const {
    return &::flatbuffers::CastToArray(a_);
  }
  ::flatbuffers::Array<uint8_t, 4> *mutable_a() {
    return &::flatbuffers::CastToArray(a_);
  }
  bool KeyCompareLessThan(const Baz * const o) const {
    return KeyCompareWithValue(o->a()) < 0;
  }
  int KeyCompareWithValue(const flatbuffers::Array<uint8_t, 4> *_a) const {
    const flatbuffers::Array<uint8_t, 4> *curr_a = a();
    for (flatbuffers::uoffset_t i = 0; i < curr_a->size(); i++) {
      const auto lhs = curr_a->Get(i);
      const auto rhs = _a->Get(i);
      if (lhs != rhs)
        return static_cast<int>(lhs > rhs) - static_cast<int>(lhs < rhs);
    }
    return 0;
  }
  uint8_t b() const {
    return ::flatbuffers::EndianScalar(b_);
  }
  void mutate_b(uint8_t _b) {
    ::flatbuffers::WriteScalar(&b_, _b);
  }
};
FLATBUFFERS_STRUCT_END(Baz, 5);

inline bool operator==(const Baz &lhs, const Baz &rhs) {
  return
      (*lhs.a() == *rhs.a()) &&
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
  static const ::flatbuffers::TypeTable *MiniReflectTypeTable() {
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
        b_(::flatbuffers::EndianScalar(_b)),
        padding0__(0),
        padding1__(0) {
    (void)padding0__;
    (void)padding1__;
  }
  Bar(::flatbuffers::span<const float, 3> _a, uint8_t _b)
      : b_(::flatbuffers::EndianScalar(_b)),
        padding0__(0),
        padding1__(0) {
    ::flatbuffers::CastToArray(a_).CopyFromSpan(_a);
    (void)padding0__;
    (void)padding1__;
  }
  const ::flatbuffers::Array<float, 3> *a() const {
    return &::flatbuffers::CastToArray(a_);
  }
  ::flatbuffers::Array<float, 3> *mutable_a() {
    return &::flatbuffers::CastToArray(a_);
  }
  bool KeyCompareLessThan(const Bar * const o) const {
    return KeyCompareWithValue(o->a()) < 0;
  }
  int KeyCompareWithValue(const flatbuffers::Array<float, 3> *_a) const {
    const flatbuffers::Array<float, 3> *curr_a = a();
    for (flatbuffers::uoffset_t i = 0; i < curr_a->size(); i++) {
      const auto lhs = curr_a->Get(i);
      const auto rhs = _a->Get(i);
      if (lhs != rhs)
        return static_cast<int>(lhs > rhs) - static_cast<int>(lhs < rhs);
    }
    return 0;
  }
  uint8_t b() const {
    return ::flatbuffers::EndianScalar(b_);
  }
  void mutate_b(uint8_t _b) {
    ::flatbuffers::WriteScalar(&b_, _b);
  }
};
FLATBUFFERS_STRUCT_END(Bar, 16);

inline bool operator==(const Bar &lhs, const Bar &rhs) {
  return
      (*lhs.a() == *rhs.a()) &&
      (lhs.b() == rhs.b());
}

inline bool operator!=(const Bar &lhs, const Bar &rhs) {
    return !(lhs == rhs);
}


FLATBUFFERS_MANUALLY_ALIGNED_STRUCT(4) Color FLATBUFFERS_FINAL_CLASS {
 private:
  float rgb_[3];
  uint8_t tag_;
  int8_t padding0__;  int16_t padding1__;

 public:
  static const ::flatbuffers::TypeTable *MiniReflectTypeTable() {
    return ColorTypeTable();
  }
  Color()
      : rgb_(),
        tag_(0),
        padding0__(0),
        padding1__(0) {
    (void)padding0__;
    (void)padding1__;
  }
  Color(uint8_t _tag)
      : rgb_(),
        tag_(::flatbuffers::EndianScalar(_tag)),
        padding0__(0),
        padding1__(0) {
    (void)padding0__;
    (void)padding1__;
  }
  Color(::flatbuffers::span<const float, 3> _rgb, uint8_t _tag)
      : tag_(::flatbuffers::EndianScalar(_tag)),
        padding0__(0),
        padding1__(0) {
    ::flatbuffers::CastToArray(rgb_).CopyFromSpan(_rgb);
    (void)padding0__;
    (void)padding1__;
  }
  const ::flatbuffers::Array<float, 3> *rgb() const {
    return &::flatbuffers::CastToArray(rgb_);
  }
  ::flatbuffers::Array<float, 3> *mutable_rgb() {
    return &::flatbuffers::CastToArray(rgb_);
  }
  bool KeyCompareLessThan(const Color * const o) const {
    return KeyCompareWithValue(o->rgb()) < 0;
  }
  int KeyCompareWithValue(const flatbuffers::Array<float, 3> *_rgb) const {
    const flatbuffers::Array<float, 3> *curr_rgb = rgb();
    for (flatbuffers::uoffset_t i = 0; i < curr_rgb->size(); i++) {
      const auto lhs = curr_rgb->Get(i);
      const auto rhs = _rgb->Get(i);
      if (lhs != rhs)
        return static_cast<int>(lhs > rhs) - static_cast<int>(lhs < rhs);
    }
    return 0;
  }
  uint8_t tag() const {
    return ::flatbuffers::EndianScalar(tag_);
  }
  void mutate_tag(uint8_t _tag) {
    ::flatbuffers::WriteScalar(&tag_, _tag);
  }
};
FLATBUFFERS_STRUCT_END(Color, 16);

inline bool operator==(const Color &lhs, const Color &rhs) {
  return
      (*lhs.rgb() == *rhs.rgb()) &&
      (lhs.tag() == rhs.tag());
}

inline bool operator!=(const Color &lhs, const Color &rhs) {
    return !(lhs == rhs);
}


FLATBUFFERS_MANUALLY_ALIGNED_STRUCT(4) Apple FLATBUFFERS_FINAL_CLASS {
 private:
  uint8_t tag_;
  int8_t padding0__;  int16_t padding1__;
  keyfield::sample::Color color_;

 public:
  static const ::flatbuffers::TypeTable *MiniReflectTypeTable() {
    return AppleTypeTable();
  }
  Apple()
      : tag_(0),
        padding0__(0),
        padding1__(0),
        color_() {
    (void)padding0__;
    (void)padding1__;
  }
  Apple(uint8_t _tag, const keyfield::sample::Color &_color)
      : tag_(::flatbuffers::EndianScalar(_tag)),
        padding0__(0),
        padding1__(0),
        color_(_color) {
    (void)padding0__;
    (void)padding1__;
  }
  uint8_t tag() const {
    return ::flatbuffers::EndianScalar(tag_);
  }
  void mutate_tag(uint8_t _tag) {
    ::flatbuffers::WriteScalar(&tag_, _tag);
  }
  const keyfield::sample::Color &color() const {
    return color_;
  }
  keyfield::sample::Color &mutable_color() {
    return color_;
  }
  bool KeyCompareLessThan(const Apple * const o) const {
    return KeyCompareWithValue(o->color()) < 0;
  }
  int KeyCompareWithValue(const keyfield::sample::Color &_color) const {
    const auto &lhs_color = color();
    const auto &rhs_color = _color;
    const auto rhs_color_rgb = rhs_color.rgb();
    const auto rgb_compare_result = lhs_color.KeyCompareWithValue(rhs_color_rgb);
    if (rgb_compare_result != 0)
      return rgb_compare_result;
    const auto lhs_color_tag = lhs_color.tag();
    const auto rhs_color_tag = rhs_color.tag();
    if (lhs_color_tag !=  rhs_color_tag)
      return static_cast<int>(lhs_color_tag > rhs_color_tag) - static_cast<int>(lhs_color_tag < rhs_color_tag);
    return 0;
  }
};
FLATBUFFERS_STRUCT_END(Apple, 20);

inline bool operator==(const Apple &lhs, const Apple &rhs) {
  return
      (lhs.tag() == rhs.tag()) &&
      (lhs.color() == rhs.color());
}

inline bool operator!=(const Apple &lhs, const Apple &rhs) {
    return !(lhs == rhs);
}


FLATBUFFERS_MANUALLY_ALIGNED_STRUCT(4) Fruit FLATBUFFERS_FINAL_CLASS {
 private:
  keyfield::sample::Apple a_;
  uint8_t b_;
  int8_t padding0__;  int16_t padding1__;

 public:
  static const ::flatbuffers::TypeTable *MiniReflectTypeTable() {
    return FruitTypeTable();
  }
  Fruit()
      : a_(),
        b_(0),
        padding0__(0),
        padding1__(0) {
    (void)padding0__;
    (void)padding1__;
  }
  Fruit(const keyfield::sample::Apple &_a, uint8_t _b)
      : a_(_a),
        b_(::flatbuffers::EndianScalar(_b)),
        padding0__(0),
        padding1__(0) {
    (void)padding0__;
    (void)padding1__;
  }
  const keyfield::sample::Apple &a() const {
    return a_;
  }
  keyfield::sample::Apple &mutable_a() {
    return a_;
  }
  bool KeyCompareLessThan(const Fruit * const o) const {
    return KeyCompareWithValue(o->a()) < 0;
  }
  int KeyCompareWithValue(const keyfield::sample::Apple &_a) const {
    const auto &lhs_a = a();
    const auto &rhs_a = _a;
    const auto lhs_a_tag = lhs_a.tag();
    const auto rhs_a_tag = rhs_a.tag();
    if (lhs_a_tag !=  rhs_a_tag)
      return static_cast<int>(lhs_a_tag > rhs_a_tag) - static_cast<int>(lhs_a_tag < rhs_a_tag);
    const auto rhs_a_color = rhs_a.color();
    const auto color_compare_result = lhs_a.KeyCompareWithValue(rhs_a_color);
    if (color_compare_result != 0)
      return color_compare_result;
    return 0;
  }
  uint8_t b() const {
    return ::flatbuffers::EndianScalar(b_);
  }
  void mutate_b(uint8_t _b) {
    ::flatbuffers::WriteScalar(&b_, _b);
  }
};
FLATBUFFERS_STRUCT_END(Fruit, 24);

inline bool operator==(const Fruit &lhs, const Fruit &rhs) {
  return
      (lhs.a() == rhs.a()) &&
      (lhs.b() == rhs.b());
}

inline bool operator!=(const Fruit &lhs, const Fruit &rhs) {
    return !(lhs == rhs);
}


FLATBUFFERS_MANUALLY_ALIGNED_STRUCT(4) Rice FLATBUFFERS_FINAL_CLASS {
 private:
  uint8_t origin_[3];
  int8_t padding0__;
  uint32_t quantity_;

 public:
  static const ::flatbuffers::TypeTable *MiniReflectTypeTable() {
    return RiceTypeTable();
  }
  Rice()
      : origin_(),
        padding0__(0),
        quantity_(0) {
    (void)padding0__;
  }
  Rice(uint32_t _quantity)
      : origin_(),
        padding0__(0),
        quantity_(::flatbuffers::EndianScalar(_quantity)) {
    (void)padding0__;
  }
  Rice(::flatbuffers::span<const uint8_t, 3> _origin, uint32_t _quantity)
      : padding0__(0),
        quantity_(::flatbuffers::EndianScalar(_quantity)) {
    ::flatbuffers::CastToArray(origin_).CopyFromSpan(_origin);
    (void)padding0__;
  }
  const ::flatbuffers::Array<uint8_t, 3> *origin() const {
    return &::flatbuffers::CastToArray(origin_);
  }
  ::flatbuffers::Array<uint8_t, 3> *mutable_origin() {
    return &::flatbuffers::CastToArray(origin_);
  }
  uint32_t quantity() const {
    return ::flatbuffers::EndianScalar(quantity_);
  }
  void mutate_quantity(uint32_t _quantity) {
    ::flatbuffers::WriteScalar(&quantity_, _quantity);
  }
};
FLATBUFFERS_STRUCT_END(Rice, 8);

inline bool operator==(const Rice &lhs, const Rice &rhs) {
  return
      (*lhs.origin() == *rhs.origin()) &&
      (lhs.quantity() == rhs.quantity());
}

inline bool operator!=(const Rice &lhs, const Rice &rhs) {
    return !(lhs == rhs);
}


FLATBUFFERS_MANUALLY_ALIGNED_STRUCT(4) Grain FLATBUFFERS_FINAL_CLASS {
 private:
  keyfield::sample::Rice a_[3];
  uint8_t tag_;
  int8_t padding0__;  int16_t padding1__;

 public:
  static const ::flatbuffers::TypeTable *MiniReflectTypeTable() {
    return GrainTypeTable();
  }
  Grain()
      : a_(),
        tag_(0),
        padding0__(0),
        padding1__(0) {
    (void)padding0__;
    (void)padding1__;
  }
  Grain(uint8_t _tag)
      : a_(),
        tag_(::flatbuffers::EndianScalar(_tag)),
        padding0__(0),
        padding1__(0) {
    (void)padding0__;
    (void)padding1__;
  }
  Grain(::flatbuffers::span<const keyfield::sample::Rice, 3> _a, uint8_t _tag)
      : tag_(::flatbuffers::EndianScalar(_tag)),
        padding0__(0),
        padding1__(0) {
    ::flatbuffers::CastToArray(a_).CopyFromSpan(_a);
    (void)padding0__;
    (void)padding1__;
  }
  const ::flatbuffers::Array<keyfield::sample::Rice, 3> *a() const {
    return &::flatbuffers::CastToArray(a_);
  }
  ::flatbuffers::Array<keyfield::sample::Rice, 3> *mutable_a() {
    return &::flatbuffers::CastToArray(a_);
  }
  bool KeyCompareLessThan(const Grain * const o) const {
    return KeyCompareWithValue(o->a()) < 0;
  }
  int KeyCompareWithValue(const flatbuffers::Array<keyfield::sample::Rice , 3> *_a) const {
    const flatbuffers::Array<keyfield::sample::Rice , 3> *curr_a = a();
    for (flatbuffers::uoffset_t i = 0; i < curr_a->size(); i++) {
      const auto &lhs_a = *(curr_a->Get(i));
      const auto &rhs_a = *(_a->Get(i));
      const auto lhs_a_origin = lhs_a.origin();
      const auto rhs_a_origin = rhs_a.origin();
      for (flatbuffers::uoffset_t i = 0; i < lhs_a_origin->size(); i++) {
        const auto lhs_a_origin_elem = lhs_a_origin->Get(i);
        const auto rhs_a_origin_elem = rhs_a_origin->Get(i);
        if (lhs_a_origin_elem != rhs_a_origin_elem)
          return static_cast<int>(lhs_a_origin_elem > rhs_a_origin_elem) - static_cast<int>(lhs_a_origin_elem < rhs_a_origin_elem);
      }
      const auto lhs_a_quantity = lhs_a.quantity();
      const auto rhs_a_quantity = rhs_a.quantity();
      if (lhs_a_quantity !=  rhs_a_quantity)
        return static_cast<int>(lhs_a_quantity > rhs_a_quantity) - static_cast<int>(lhs_a_quantity < rhs_a_quantity);
    }
    return 0;
  }
  uint8_t tag() const {
    return ::flatbuffers::EndianScalar(tag_);
  }
  void mutate_tag(uint8_t _tag) {
    ::flatbuffers::WriteScalar(&tag_, _tag);
  }
};
FLATBUFFERS_STRUCT_END(Grain, 28);

inline bool operator==(const Grain &lhs, const Grain &rhs) {
  return
      (*lhs.a() == *rhs.a()) &&
      (lhs.tag() == rhs.tag());
}

inline bool operator!=(const Grain &lhs, const Grain &rhs) {
    return !(lhs == rhs);
}


struct FooTableT : public ::flatbuffers::NativeTable {
  typedef FooTable TableType;
  int32_t a = 0;
  int32_t b = 0;
  std::string c{};
  std::vector<keyfield::sample::Baz> d{};
  std::vector<keyfield::sample::Bar> e{};
  std::vector<keyfield::sample::Apple> f{};
  std::vector<keyfield::sample::Fruit> g{};
  std::vector<keyfield::sample::Grain> h{};
};

struct FooTable FLATBUFFERS_FINAL_CLASS : private ::flatbuffers::Table {
  typedef FooTableT NativeTableType;
  typedef FooTableBuilder Builder;
  static const ::flatbuffers::TypeTable *MiniReflectTypeTable() {
    return FooTableTypeTable();
  }
  enum FlatBuffersVTableOffset FLATBUFFERS_VTABLE_UNDERLYING_TYPE {
    VT_A = 4,
    VT_B = 6,
    VT_C = 8,
    VT_D = 10,
    VT_E = 12,
    VT_F = 14,
    VT_G = 16,
    VT_H = 18
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
  const ::flatbuffers::String *c() const {
    return GetPointer<const ::flatbuffers::String *>(VT_C);
  }
  ::flatbuffers::String *mutable_c() {
    return GetPointer<::flatbuffers::String *>(VT_C);
  }
  bool KeyCompareLessThan(const FooTable * const o) const {
    return *c() < *o->c();
  }
  int KeyCompareWithValue(const char *_c) const {
    return strcmp(c()->c_str(), _c);
  }
  const ::flatbuffers::Vector<const keyfield::sample::Baz *> *d() const {
    return GetPointer<const ::flatbuffers::Vector<const keyfield::sample::Baz *> *>(VT_D);
  }
  ::flatbuffers::Vector<const keyfield::sample::Baz *> *mutable_d() {
    return GetPointer<::flatbuffers::Vector<const keyfield::sample::Baz *> *>(VT_D);
  }
  const ::flatbuffers::Vector<const keyfield::sample::Bar *> *e() const {
    return GetPointer<const ::flatbuffers::Vector<const keyfield::sample::Bar *> *>(VT_E);
  }
  ::flatbuffers::Vector<const keyfield::sample::Bar *> *mutable_e() {
    return GetPointer<::flatbuffers::Vector<const keyfield::sample::Bar *> *>(VT_E);
  }
  const ::flatbuffers::Vector<const keyfield::sample::Apple *> *f() const {
    return GetPointer<const ::flatbuffers::Vector<const keyfield::sample::Apple *> *>(VT_F);
  }
  ::flatbuffers::Vector<const keyfield::sample::Apple *> *mutable_f() {
    return GetPointer<::flatbuffers::Vector<const keyfield::sample::Apple *> *>(VT_F);
  }
  const ::flatbuffers::Vector<const keyfield::sample::Fruit *> *g() const {
    return GetPointer<const ::flatbuffers::Vector<const keyfield::sample::Fruit *> *>(VT_G);
  }
  ::flatbuffers::Vector<const keyfield::sample::Fruit *> *mutable_g() {
    return GetPointer<::flatbuffers::Vector<const keyfield::sample::Fruit *> *>(VT_G);
  }
  const ::flatbuffers::Vector<const keyfield::sample::Grain *> *h() const {
    return GetPointer<const ::flatbuffers::Vector<const keyfield::sample::Grain *> *>(VT_H);
  }
  ::flatbuffers::Vector<const keyfield::sample::Grain *> *mutable_h() {
    return GetPointer<::flatbuffers::Vector<const keyfield::sample::Grain *> *>(VT_H);
  }
  bool Verify(::flatbuffers::Verifier &verifier) const {
    return VerifyTableStart(verifier) &&
           VerifyField<int32_t>(verifier, VT_A, 4) &&
           VerifyField<int32_t>(verifier, VT_B, 4) &&
           VerifyOffsetRequired(verifier, VT_C) &&
           verifier.VerifyString(c()) &&
           VerifyOffset(verifier, VT_D) &&
           verifier.VerifyVector(d()) &&
           VerifyOffset(verifier, VT_E) &&
           verifier.VerifyVector(e()) &&
           VerifyOffset(verifier, VT_F) &&
           verifier.VerifyVector(f()) &&
           VerifyOffset(verifier, VT_G) &&
           verifier.VerifyVector(g()) &&
           VerifyOffset(verifier, VT_H) &&
           verifier.VerifyVector(h()) &&
           verifier.EndTable();
  }
  FooTableT *UnPack(const ::flatbuffers::resolver_function_t *_resolver = nullptr) const;
  void UnPackTo(FooTableT *_o, const ::flatbuffers::resolver_function_t *_resolver = nullptr) const;
  static ::flatbuffers::Offset<FooTable> Pack(::flatbuffers::FlatBufferBuilder &_fbb, const FooTableT* _o, const ::flatbuffers::rehasher_function_t *_rehasher = nullptr);
};

struct FooTableBuilder {
  typedef FooTable Table;
  ::flatbuffers::FlatBufferBuilder &fbb_;
  ::flatbuffers::uoffset_t start_;
  void add_a(int32_t a) {
    fbb_.AddElement<int32_t>(FooTable::VT_A, a, 0);
  }
  void add_b(int32_t b) {
    fbb_.AddElement<int32_t>(FooTable::VT_B, b, 0);
  }
  void add_c(::flatbuffers::Offset<::flatbuffers::String> c) {
    fbb_.AddOffset(FooTable::VT_C, c);
  }
  void add_d(::flatbuffers::Offset<::flatbuffers::Vector<const keyfield::sample::Baz *>> d) {
    fbb_.AddOffset(FooTable::VT_D, d);
  }
  void add_e(::flatbuffers::Offset<::flatbuffers::Vector<const keyfield::sample::Bar *>> e) {
    fbb_.AddOffset(FooTable::VT_E, e);
  }
  void add_f(::flatbuffers::Offset<::flatbuffers::Vector<const keyfield::sample::Apple *>> f) {
    fbb_.AddOffset(FooTable::VT_F, f);
  }
  void add_g(::flatbuffers::Offset<::flatbuffers::Vector<const keyfield::sample::Fruit *>> g) {
    fbb_.AddOffset(FooTable::VT_G, g);
  }
  void add_h(::flatbuffers::Offset<::flatbuffers::Vector<const keyfield::sample::Grain *>> h) {
    fbb_.AddOffset(FooTable::VT_H, h);
  }
  explicit FooTableBuilder(::flatbuffers::FlatBufferBuilder &_fbb)
        : fbb_(_fbb) {
    start_ = fbb_.StartTable();
  }
  ::flatbuffers::Offset<FooTable> Finish() {
    const auto end = fbb_.EndTable(start_);
    auto o = ::flatbuffers::Offset<FooTable>(end);
    fbb_.Required(o, FooTable::VT_C);
    return o;
  }
};

inline ::flatbuffers::Offset<FooTable> CreateFooTable(
    ::flatbuffers::FlatBufferBuilder &_fbb,
    int32_t a = 0,
    int32_t b = 0,
    ::flatbuffers::Offset<::flatbuffers::String> c = 0,
    ::flatbuffers::Offset<::flatbuffers::Vector<const keyfield::sample::Baz *>> d = 0,
    ::flatbuffers::Offset<::flatbuffers::Vector<const keyfield::sample::Bar *>> e = 0,
    ::flatbuffers::Offset<::flatbuffers::Vector<const keyfield::sample::Apple *>> f = 0,
    ::flatbuffers::Offset<::flatbuffers::Vector<const keyfield::sample::Fruit *>> g = 0,
    ::flatbuffers::Offset<::flatbuffers::Vector<const keyfield::sample::Grain *>> h = 0) {
  FooTableBuilder builder_(_fbb);
  builder_.add_h(h);
  builder_.add_g(g);
  builder_.add_f(f);
  builder_.add_e(e);
  builder_.add_d(d);
  builder_.add_c(c);
  builder_.add_b(b);
  builder_.add_a(a);
  return builder_.Finish();
}

inline ::flatbuffers::Offset<FooTable> CreateFooTableDirect(
    ::flatbuffers::FlatBufferBuilder &_fbb,
    int32_t a = 0,
    int32_t b = 0,
    const char *c = nullptr,
    std::vector<keyfield::sample::Baz> *d = nullptr,
    std::vector<keyfield::sample::Bar> *e = nullptr,
    std::vector<keyfield::sample::Apple> *f = nullptr,
    std::vector<keyfield::sample::Fruit> *g = nullptr,
    std::vector<keyfield::sample::Grain> *h = nullptr) {
  auto c__ = c ? _fbb.CreateString(c) : 0;
  auto d__ = d ? _fbb.CreateVectorOfSortedStructs<keyfield::sample::Baz>(d) : 0;
  auto e__ = e ? _fbb.CreateVectorOfSortedStructs<keyfield::sample::Bar>(e) : 0;
  auto f__ = f ? _fbb.CreateVectorOfSortedStructs<keyfield::sample::Apple>(f) : 0;
  auto g__ = g ? _fbb.CreateVectorOfSortedStructs<keyfield::sample::Fruit>(g) : 0;
  auto h__ = h ? _fbb.CreateVectorOfSortedStructs<keyfield::sample::Grain>(h) : 0;
  return keyfield::sample::CreateFooTable(
      _fbb,
      a,
      b,
      c__,
      d__,
      e__,
      f__,
      g__,
      h__);
}

::flatbuffers::Offset<FooTable> CreateFooTable(::flatbuffers::FlatBufferBuilder &_fbb, const FooTableT *_o, const ::flatbuffers::rehasher_function_t *_rehasher = nullptr);


inline bool operator==(const FooTableT &lhs, const FooTableT &rhs) {
  return
      (lhs.a == rhs.a) &&
      (lhs.b == rhs.b) &&
      (lhs.c == rhs.c) &&
      (lhs.d == rhs.d) &&
      (lhs.e == rhs.e) &&
      (lhs.f == rhs.f) &&
      (lhs.g == rhs.g) &&
      (lhs.h == rhs.h);
}

inline bool operator!=(const FooTableT &lhs, const FooTableT &rhs) {
    return !(lhs == rhs);
}


inline FooTableT *FooTable::UnPack(const ::flatbuffers::resolver_function_t *_resolver) const {
  auto _o = std::unique_ptr<FooTableT>(new FooTableT());
  UnPackTo(_o.get(), _resolver);
  return _o.release();
}

inline void FooTable::UnPackTo(FooTableT *_o, const ::flatbuffers::resolver_function_t *_resolver) const {
  (void)_o;
  (void)_resolver;
  { auto _e = a(); _o->a = _e; }
  { auto _e = b(); _o->b = _e; }
  { auto _e = c(); if (_e) _o->c = _e->str(); }
  { auto _e = d(); if (_e) { _o->d.resize(_e->size()); for (::flatbuffers::uoffset_t _i = 0; _i < _e->size(); _i++) { _o->d[_i] = *_e->Get(_i); } } else { _o->d.resize(0); } }
  { auto _e = e(); if (_e) { _o->e.resize(_e->size()); for (::flatbuffers::uoffset_t _i = 0; _i < _e->size(); _i++) { _o->e[_i] = *_e->Get(_i); } } else { _o->e.resize(0); } }
  { auto _e = f(); if (_e) { _o->f.resize(_e->size()); for (::flatbuffers::uoffset_t _i = 0; _i < _e->size(); _i++) { _o->f[_i] = *_e->Get(_i); } } else { _o->f.resize(0); } }
  { auto _e = g(); if (_e) { _o->g.resize(_e->size()); for (::flatbuffers::uoffset_t _i = 0; _i < _e->size(); _i++) { _o->g[_i] = *_e->Get(_i); } } else { _o->g.resize(0); } }
  { auto _e = h(); if (_e) { _o->h.resize(_e->size()); for (::flatbuffers::uoffset_t _i = 0; _i < _e->size(); _i++) { _o->h[_i] = *_e->Get(_i); } } else { _o->h.resize(0); } }
}

inline ::flatbuffers::Offset<FooTable> FooTable::Pack(::flatbuffers::FlatBufferBuilder &_fbb, const FooTableT* _o, const ::flatbuffers::rehasher_function_t *_rehasher) {
  return CreateFooTable(_fbb, _o, _rehasher);
}

inline ::flatbuffers::Offset<FooTable> CreateFooTable(::flatbuffers::FlatBufferBuilder &_fbb, const FooTableT *_o, const ::flatbuffers::rehasher_function_t *_rehasher) {
  (void)_rehasher;
  (void)_o;
  struct _VectorArgs { ::flatbuffers::FlatBufferBuilder *__fbb; const FooTableT* __o; const ::flatbuffers::rehasher_function_t *__rehasher; } _va = { &_fbb, _o, _rehasher}; (void)_va;
  auto _a = _o->a;
  auto _b = _o->b;
  auto _c = _fbb.CreateString(_o->c);
  auto _d = _o->d.size() ? _fbb.CreateVectorOfStructs(_o->d) : 0;
  auto _e = _o->e.size() ? _fbb.CreateVectorOfStructs(_o->e) : 0;
  auto _f = _o->f.size() ? _fbb.CreateVectorOfStructs(_o->f) : 0;
  auto _g = _o->g.size() ? _fbb.CreateVectorOfStructs(_o->g) : 0;
  auto _h = _o->h.size() ? _fbb.CreateVectorOfStructs(_o->h) : 0;
  return keyfield::sample::CreateFooTable(
      _fbb,
      _a,
      _b,
      _c,
      _d,
      _e,
      _f,
      _g,
      _h);
}

inline const ::flatbuffers::TypeTable *BazTypeTable() {
  static const ::flatbuffers::TypeCode type_codes[] = {
    { ::flatbuffers::ET_UCHAR, 1, -1 },
    { ::flatbuffers::ET_UCHAR, 0, -1 }
  };
  static const int16_t array_sizes[] = { 4,  };
  static const int64_t values[] = { 0, 4, 5 };
  static const char * const names[] = {
    "a",
    "b"
  };
  static const ::flatbuffers::TypeTable tt = {
    ::flatbuffers::ST_STRUCT, 2, type_codes, nullptr, array_sizes, values, names
  };
  return &tt;
}

inline const ::flatbuffers::TypeTable *BarTypeTable() {
  static const ::flatbuffers::TypeCode type_codes[] = {
    { ::flatbuffers::ET_FLOAT, 1, -1 },
    { ::flatbuffers::ET_UCHAR, 0, -1 }
  };
  static const int16_t array_sizes[] = { 3,  };
  static const int64_t values[] = { 0, 12, 16 };
  static const char * const names[] = {
    "a",
    "b"
  };
  static const ::flatbuffers::TypeTable tt = {
    ::flatbuffers::ST_STRUCT, 2, type_codes, nullptr, array_sizes, values, names
  };
  return &tt;
}

inline const ::flatbuffers::TypeTable *ColorTypeTable() {
  static const ::flatbuffers::TypeCode type_codes[] = {
    { ::flatbuffers::ET_FLOAT, 1, -1 },
    { ::flatbuffers::ET_UCHAR, 0, -1 }
  };
  static const int16_t array_sizes[] = { 3,  };
  static const int64_t values[] = { 0, 12, 16 };
  static const char * const names[] = {
    "rgb",
    "tag"
  };
  static const ::flatbuffers::TypeTable tt = {
    ::flatbuffers::ST_STRUCT, 2, type_codes, nullptr, array_sizes, values, names
  };
  return &tt;
}

inline const ::flatbuffers::TypeTable *AppleTypeTable() {
  static const ::flatbuffers::TypeCode type_codes[] = {
    { ::flatbuffers::ET_UCHAR, 0, -1 },
    { ::flatbuffers::ET_SEQUENCE, 0, 0 }
  };
  static const ::flatbuffers::TypeFunction type_refs[] = {
    keyfield::sample::ColorTypeTable
  };
  static const int64_t values[] = { 0, 4, 20 };
  static const char * const names[] = {
    "tag",
    "color"
  };
  static const ::flatbuffers::TypeTable tt = {
    ::flatbuffers::ST_STRUCT, 2, type_codes, type_refs, nullptr, values, names
  };
  return &tt;
}

inline const ::flatbuffers::TypeTable *FruitTypeTable() {
  static const ::flatbuffers::TypeCode type_codes[] = {
    { ::flatbuffers::ET_SEQUENCE, 0, 0 },
    { ::flatbuffers::ET_UCHAR, 0, -1 }
  };
  static const ::flatbuffers::TypeFunction type_refs[] = {
    keyfield::sample::AppleTypeTable
  };
  static const int64_t values[] = { 0, 20, 24 };
  static const char * const names[] = {
    "a",
    "b"
  };
  static const ::flatbuffers::TypeTable tt = {
    ::flatbuffers::ST_STRUCT, 2, type_codes, type_refs, nullptr, values, names
  };
  return &tt;
}

inline const ::flatbuffers::TypeTable *RiceTypeTable() {
  static const ::flatbuffers::TypeCode type_codes[] = {
    { ::flatbuffers::ET_UCHAR, 1, -1 },
    { ::flatbuffers::ET_UINT, 0, -1 }
  };
  static const int16_t array_sizes[] = { 3,  };
  static const int64_t values[] = { 0, 4, 8 };
  static const char * const names[] = {
    "origin",
    "quantity"
  };
  static const ::flatbuffers::TypeTable tt = {
    ::flatbuffers::ST_STRUCT, 2, type_codes, nullptr, array_sizes, values, names
  };
  return &tt;
}

inline const ::flatbuffers::TypeTable *GrainTypeTable() {
  static const ::flatbuffers::TypeCode type_codes[] = {
    { ::flatbuffers::ET_SEQUENCE, 1, 0 },
    { ::flatbuffers::ET_UCHAR, 0, -1 }
  };
  static const ::flatbuffers::TypeFunction type_refs[] = {
    keyfield::sample::RiceTypeTable
  };
  static const int16_t array_sizes[] = { 3,  };
  static const int64_t values[] = { 0, 24, 28 };
  static const char * const names[] = {
    "a",
    "tag"
  };
  static const ::flatbuffers::TypeTable tt = {
    ::flatbuffers::ST_STRUCT, 2, type_codes, type_refs, array_sizes, values, names
  };
  return &tt;
}

inline const ::flatbuffers::TypeTable *FooTableTypeTable() {
  static const ::flatbuffers::TypeCode type_codes[] = {
    { ::flatbuffers::ET_INT, 0, -1 },
    { ::flatbuffers::ET_INT, 0, -1 },
    { ::flatbuffers::ET_STRING, 0, -1 },
    { ::flatbuffers::ET_SEQUENCE, 1, 0 },
    { ::flatbuffers::ET_SEQUENCE, 1, 1 },
    { ::flatbuffers::ET_SEQUENCE, 1, 2 },
    { ::flatbuffers::ET_SEQUENCE, 1, 3 },
    { ::flatbuffers::ET_SEQUENCE, 1, 4 }
  };
  static const ::flatbuffers::TypeFunction type_refs[] = {
    keyfield::sample::BazTypeTable,
    keyfield::sample::BarTypeTable,
    keyfield::sample::AppleTypeTable,
    keyfield::sample::FruitTypeTable,
    keyfield::sample::GrainTypeTable
  };
  static const char * const names[] = {
    "a",
    "b",
    "c",
    "d",
    "e",
    "f",
    "g",
    "h"
  };
  static const ::flatbuffers::TypeTable tt = {
    ::flatbuffers::ST_TABLE, 8, type_codes, type_refs, nullptr, nullptr, names
  };
  return &tt;
}

inline const keyfield::sample::FooTable *GetFooTable(const void *buf) {
  return ::flatbuffers::GetRoot<keyfield::sample::FooTable>(buf);
}

inline const keyfield::sample::FooTable *GetSizePrefixedFooTable(const void *buf) {
  return ::flatbuffers::GetSizePrefixedRoot<keyfield::sample::FooTable>(buf);
}

inline FooTable *GetMutableFooTable(void *buf) {
  return ::flatbuffers::GetMutableRoot<FooTable>(buf);
}

inline keyfield::sample::FooTable *GetMutableSizePrefixedFooTable(void *buf) {
  return ::flatbuffers::GetMutableSizePrefixedRoot<keyfield::sample::FooTable>(buf);
}

inline bool VerifyFooTableBuffer(
    ::flatbuffers::Verifier &verifier) {
  return verifier.VerifyBuffer<keyfield::sample::FooTable>(nullptr);
}

inline bool VerifySizePrefixedFooTableBuffer(
    ::flatbuffers::Verifier &verifier) {
  return verifier.VerifySizePrefixedBuffer<keyfield::sample::FooTable>(nullptr);
}

inline void FinishFooTableBuffer(
    ::flatbuffers::FlatBufferBuilder &fbb,
    ::flatbuffers::Offset<keyfield::sample::FooTable> root) {
  fbb.Finish(root);
}

inline void FinishSizePrefixedFooTableBuffer(
    ::flatbuffers::FlatBufferBuilder &fbb,
    ::flatbuffers::Offset<keyfield::sample::FooTable> root) {
  fbb.FinishSizePrefixed(root);
}

inline flatbuffers::unique_ptr<keyfield::sample::FooTableT> UnPackFooTable(
    const void *buf,
    const ::flatbuffers::resolver_function_t *res = nullptr) {
  return flatbuffers::unique_ptr<keyfield::sample::FooTableT>(GetFooTable(buf)->UnPack(res));
}

inline flatbuffers::unique_ptr<keyfield::sample::FooTableT> UnPackSizePrefixedFooTable(
    const void *buf,
    const ::flatbuffers::resolver_function_t *res = nullptr) {
  return flatbuffers::unique_ptr<keyfield::sample::FooTableT>(GetSizePrefixedFooTable(buf)->UnPack(res));
}

}  // namespace sample
}  // namespace keyfield

#endif  // FLATBUFFERS_GENERATED_KEYFIELDSAMPLE_KEYFIELD_SAMPLE_H_
