// automatically generated by the FlatBuffers compiler, do not modify


#ifndef FLATBUFFERS_GENERATED_ALIGNMENTTEST_H_
#define FLATBUFFERS_GENERATED_ALIGNMENTTEST_H_

#include "flatbuffers/flatbuffers.h"

// Ensure the included flatbuffers.h is the same version as when this file was
// generated, otherwise it may not be compatible.
static_assert(FLATBUFFERS_VERSION_MAJOR == 22 &&
              FLATBUFFERS_VERSION_MINOR == 11 &&
              FLATBUFFERS_VERSION_REVISION == 22,
             "Non-compatible flatbuffers version included");

struct BadAlignmentSmall;

struct BadAlignmentLarge;

struct OuterLarge;
struct OuterLargeBuilder;
struct OuterLargeT;

struct BadAlignmentRoot;
struct BadAlignmentRootBuilder;
struct BadAlignmentRootT;

bool operator==(const BadAlignmentSmall &lhs, const BadAlignmentSmall &rhs);
bool operator!=(const BadAlignmentSmall &lhs, const BadAlignmentSmall &rhs);
bool operator==(const BadAlignmentLarge &lhs, const BadAlignmentLarge &rhs);
bool operator!=(const BadAlignmentLarge &lhs, const BadAlignmentLarge &rhs);
bool operator==(const OuterLargeT &lhs, const OuterLargeT &rhs);
bool operator!=(const OuterLargeT &lhs, const OuterLargeT &rhs);
bool operator==(const BadAlignmentRootT &lhs, const BadAlignmentRootT &rhs);
bool operator!=(const BadAlignmentRootT &lhs, const BadAlignmentRootT &rhs);

inline const flatbuffers::TypeTable *BadAlignmentSmallTypeTable();

inline const flatbuffers::TypeTable *BadAlignmentLargeTypeTable();

inline const flatbuffers::TypeTable *OuterLargeTypeTable();

inline const flatbuffers::TypeTable *BadAlignmentRootTypeTable();

FLATBUFFERS_MANUALLY_ALIGNED_STRUCT(4) BadAlignmentSmall FLATBUFFERS_FINAL_CLASS {
 private:
  uint32_t var_0_;
  uint32_t var_1_;
  uint32_t var_2_;

 public:
  static const flatbuffers::TypeTable *MiniReflectTypeTable() {
    return BadAlignmentSmallTypeTable();
  }
  BadAlignmentSmall()
      : var_0_(0),
        var_1_(0),
        var_2_(0) {
  }
  BadAlignmentSmall(uint32_t _var_0, uint32_t _var_1, uint32_t _var_2)
      : var_0_(flatbuffers::EndianScalar(_var_0)),
        var_1_(flatbuffers::EndianScalar(_var_1)),
        var_2_(flatbuffers::EndianScalar(_var_2)) {
  }
  uint32_t var_0() const {
    return flatbuffers::EndianScalar(var_0_);
  }
  void mutate_var_0(uint32_t _var_0) {
    flatbuffers::WriteScalar(&var_0_, _var_0);
  }
  uint32_t var_1() const {
    return flatbuffers::EndianScalar(var_1_);
  }
  void mutate_var_1(uint32_t _var_1) {
    flatbuffers::WriteScalar(&var_1_, _var_1);
  }
  uint32_t var_2() const {
    return flatbuffers::EndianScalar(var_2_);
  }
  void mutate_var_2(uint32_t _var_2) {
    flatbuffers::WriteScalar(&var_2_, _var_2);
  }
};
FLATBUFFERS_STRUCT_END(BadAlignmentSmall, 12);

inline bool operator==(const BadAlignmentSmall &lhs, const BadAlignmentSmall &rhs) {
  return
      (lhs.var_0() == rhs.var_0()) &&
      (lhs.var_1() == rhs.var_1()) &&
      (lhs.var_2() == rhs.var_2());
}

inline bool operator!=(const BadAlignmentSmall &lhs, const BadAlignmentSmall &rhs) {
    return !(lhs == rhs);
}


FLATBUFFERS_MANUALLY_ALIGNED_STRUCT(8) BadAlignmentLarge FLATBUFFERS_FINAL_CLASS {
 private:
  uint64_t var_0_;

 public:
  static const flatbuffers::TypeTable *MiniReflectTypeTable() {
    return BadAlignmentLargeTypeTable();
  }
  BadAlignmentLarge()
      : var_0_(0) {
  }
  BadAlignmentLarge(uint64_t _var_0)
      : var_0_(flatbuffers::EndianScalar(_var_0)) {
  }
  uint64_t var_0() const {
    return flatbuffers::EndianScalar(var_0_);
  }
  void mutate_var_0(uint64_t _var_0) {
    flatbuffers::WriteScalar(&var_0_, _var_0);
  }
};
FLATBUFFERS_STRUCT_END(BadAlignmentLarge, 8);

inline bool operator==(const BadAlignmentLarge &lhs, const BadAlignmentLarge &rhs) {
  return
      (lhs.var_0() == rhs.var_0());
}

inline bool operator!=(const BadAlignmentLarge &lhs, const BadAlignmentLarge &rhs) {
    return !(lhs == rhs);
}


struct OuterLargeT : public flatbuffers::NativeTable {
  typedef OuterLarge TableType;
  flatbuffers::unique_ptr<BadAlignmentLarge> large{};
  OuterLargeT() = default;
  OuterLargeT(const OuterLargeT &o);
  OuterLargeT(OuterLargeT&&) FLATBUFFERS_NOEXCEPT = default;
  OuterLargeT &operator=(OuterLargeT o) FLATBUFFERS_NOEXCEPT;
};

struct OuterLarge FLATBUFFERS_FINAL_CLASS : private flatbuffers::Table {
  typedef OuterLargeT NativeTableType;
  typedef OuterLargeBuilder Builder;
  static const flatbuffers::TypeTable *MiniReflectTypeTable() {
    return OuterLargeTypeTable();
  }
  enum FlatBuffersVTableOffset FLATBUFFERS_VTABLE_UNDERLYING_TYPE {
    VT_LARGE = 4
  };
  const BadAlignmentLarge *large() const {
    return GetStruct<const BadAlignmentLarge *>(VT_LARGE);
  }
  BadAlignmentLarge *mutable_large() {
    return GetStruct<BadAlignmentLarge *>(VT_LARGE);
  }
  bool Verify(flatbuffers::Verifier &verifier) const {
    return VerifyTableStart(verifier) &&
           VerifyField<BadAlignmentLarge>(verifier, VT_LARGE, 8) &&
           verifier.EndTable();
  }
  OuterLargeT *UnPack(const flatbuffers::resolver_function_t *_resolver = nullptr) const;
  void UnPackTo(OuterLargeT *_o, const flatbuffers::resolver_function_t *_resolver = nullptr) const;
  static flatbuffers::Offset<OuterLarge> Pack(flatbuffers::FlatBufferBuilder &_fbb, const OuterLargeT* _o, const flatbuffers::rehasher_function_t *_rehasher = nullptr);
};

struct OuterLargeBuilder {
  typedef OuterLarge Table;
  flatbuffers::FlatBufferBuilder &fbb_;
  flatbuffers::uoffset_t start_;
  void add_large(const BadAlignmentLarge *large) {
    fbb_.AddStruct(OuterLarge::VT_LARGE, large);
  }
  explicit OuterLargeBuilder(flatbuffers::FlatBufferBuilder &_fbb)
        : fbb_(_fbb) {
    start_ = fbb_.StartTable();
  }
  flatbuffers::Offset<OuterLarge> Finish() {
    const auto end = fbb_.EndTable(start_);
    auto o = flatbuffers::Offset<OuterLarge>(end);
    return o;
  }
};

inline flatbuffers::Offset<OuterLarge> CreateOuterLarge(
    flatbuffers::FlatBufferBuilder &_fbb,
    const BadAlignmentLarge *large = nullptr) {
  OuterLargeBuilder builder_(_fbb);
  builder_.add_large(large);
  return builder_.Finish();
}

flatbuffers::Offset<OuterLarge> CreateOuterLarge(flatbuffers::FlatBufferBuilder &_fbb, const OuterLargeT *_o, const flatbuffers::rehasher_function_t *_rehasher = nullptr);

struct BadAlignmentRootT : public flatbuffers::NativeTable {
  typedef BadAlignmentRoot TableType;
  flatbuffers::unique_ptr<OuterLargeT> large{};
  std::vector<BadAlignmentSmall> small{};
  BadAlignmentRootT() = default;
  BadAlignmentRootT(const BadAlignmentRootT &o);
  BadAlignmentRootT(BadAlignmentRootT&&) FLATBUFFERS_NOEXCEPT = default;
  BadAlignmentRootT &operator=(BadAlignmentRootT o) FLATBUFFERS_NOEXCEPT;
};

struct BadAlignmentRoot FLATBUFFERS_FINAL_CLASS : private flatbuffers::Table {
  typedef BadAlignmentRootT NativeTableType;
  typedef BadAlignmentRootBuilder Builder;
  static const flatbuffers::TypeTable *MiniReflectTypeTable() {
    return BadAlignmentRootTypeTable();
  }
  enum FlatBuffersVTableOffset FLATBUFFERS_VTABLE_UNDERLYING_TYPE {
    VT_LARGE = 4,
    VT_SMALL = 6
  };
  const OuterLarge *large() const {
    return GetPointer<const OuterLarge *>(VT_LARGE);
  }
  OuterLarge *mutable_large() {
    return GetPointer<OuterLarge *>(VT_LARGE);
  }
  const flatbuffers::Vector<const BadAlignmentSmall *> *small() const {
    return GetPointer<const flatbuffers::Vector<const BadAlignmentSmall *> *>(VT_SMALL);
  }
  flatbuffers::Vector<const BadAlignmentSmall *> *mutable_small() {
    return GetPointer<flatbuffers::Vector<const BadAlignmentSmall *> *>(VT_SMALL);
  }
  bool Verify(flatbuffers::Verifier &verifier) const {
    return VerifyTableStart(verifier) &&
           VerifyOffset(verifier, VT_LARGE) &&
           verifier.VerifyTable(large()) &&
           VerifyOffset(verifier, VT_SMALL) &&
           verifier.VerifyVector(small()) &&
           verifier.EndTable();
  }
  BadAlignmentRootT *UnPack(const flatbuffers::resolver_function_t *_resolver = nullptr) const;
  void UnPackTo(BadAlignmentRootT *_o, const flatbuffers::resolver_function_t *_resolver = nullptr) const;
  static flatbuffers::Offset<BadAlignmentRoot> Pack(flatbuffers::FlatBufferBuilder &_fbb, const BadAlignmentRootT* _o, const flatbuffers::rehasher_function_t *_rehasher = nullptr);
};

struct BadAlignmentRootBuilder {
  typedef BadAlignmentRoot Table;
  flatbuffers::FlatBufferBuilder &fbb_;
  flatbuffers::uoffset_t start_;
  void add_large(flatbuffers::Offset<OuterLarge> large) {
    fbb_.AddOffset(BadAlignmentRoot::VT_LARGE, large);
  }
  void add_small(flatbuffers::Offset<flatbuffers::Vector<const BadAlignmentSmall *>> small) {
    fbb_.AddOffset(BadAlignmentRoot::VT_SMALL, small);
  }
  explicit BadAlignmentRootBuilder(flatbuffers::FlatBufferBuilder &_fbb)
        : fbb_(_fbb) {
    start_ = fbb_.StartTable();
  }
  flatbuffers::Offset<BadAlignmentRoot> Finish() {
    const auto end = fbb_.EndTable(start_);
    auto o = flatbuffers::Offset<BadAlignmentRoot>(end);
    return o;
  }
};

inline flatbuffers::Offset<BadAlignmentRoot> CreateBadAlignmentRoot(
    flatbuffers::FlatBufferBuilder &_fbb,
    flatbuffers::Offset<OuterLarge> large = 0,
    flatbuffers::Offset<flatbuffers::Vector<const BadAlignmentSmall *>> small = 0) {
  BadAlignmentRootBuilder builder_(_fbb);
  builder_.add_small(small);
  builder_.add_large(large);
  return builder_.Finish();
}

inline flatbuffers::Offset<BadAlignmentRoot> CreateBadAlignmentRootDirect(
    flatbuffers::FlatBufferBuilder &_fbb,
    flatbuffers::Offset<OuterLarge> large = 0,
    const std::vector<BadAlignmentSmall> *small = nullptr) {
  auto small__ = small ? _fbb.CreateVectorOfStructs<BadAlignmentSmall>(*small) : 0;
  return CreateBadAlignmentRoot(
      _fbb,
      large,
      small__);
}

flatbuffers::Offset<BadAlignmentRoot> CreateBadAlignmentRoot(flatbuffers::FlatBufferBuilder &_fbb, const BadAlignmentRootT *_o, const flatbuffers::rehasher_function_t *_rehasher = nullptr);


inline bool operator==(const OuterLargeT &lhs, const OuterLargeT &rhs) {
  return
      ((lhs.large == rhs.large) || (lhs.large && rhs.large && *lhs.large == *rhs.large));
}

inline bool operator!=(const OuterLargeT &lhs, const OuterLargeT &rhs) {
    return !(lhs == rhs);
}


inline OuterLargeT::OuterLargeT(const OuterLargeT &o)
      : large((o.large) ? new BadAlignmentLarge(*o.large) : nullptr) {
}

inline OuterLargeT &OuterLargeT::operator=(OuterLargeT o) FLATBUFFERS_NOEXCEPT {
  std::swap(large, o.large);
  return *this;
}

inline OuterLargeT *OuterLarge::UnPack(const flatbuffers::resolver_function_t *_resolver) const {
  auto _o = std::unique_ptr<OuterLargeT>(new OuterLargeT());
  UnPackTo(_o.get(), _resolver);
  return _o.release();
}

inline void OuterLarge::UnPackTo(OuterLargeT *_o, const flatbuffers::resolver_function_t *_resolver) const {
  (void)_o;
  (void)_resolver;
  { auto _e = large(); if (_e) _o->large = flatbuffers::unique_ptr<BadAlignmentLarge>(new BadAlignmentLarge(*_e)); }
}

inline flatbuffers::Offset<OuterLarge> OuterLarge::Pack(flatbuffers::FlatBufferBuilder &_fbb, const OuterLargeT* _o, const flatbuffers::rehasher_function_t *_rehasher) {
  return CreateOuterLarge(_fbb, _o, _rehasher);
}

inline flatbuffers::Offset<OuterLarge> CreateOuterLarge(flatbuffers::FlatBufferBuilder &_fbb, const OuterLargeT *_o, const flatbuffers::rehasher_function_t *_rehasher) {
  (void)_rehasher;
  (void)_o;
  struct _VectorArgs { flatbuffers::FlatBufferBuilder *__fbb; const OuterLargeT* __o; const flatbuffers::rehasher_function_t *__rehasher; } _va = { &_fbb, _o, _rehasher}; (void)_va;
  auto _large = _o->large ? _o->large.get() : nullptr;
  return CreateOuterLarge(
      _fbb,
      _large);
}


inline bool operator==(const BadAlignmentRootT &lhs, const BadAlignmentRootT &rhs) {
  return
      ((lhs.large == rhs.large) || (lhs.large && rhs.large && *lhs.large == *rhs.large)) &&
      (lhs.small == rhs.small);
}

inline bool operator!=(const BadAlignmentRootT &lhs, const BadAlignmentRootT &rhs) {
    return !(lhs == rhs);
}


inline BadAlignmentRootT::BadAlignmentRootT(const BadAlignmentRootT &o)
      : large((o.large) ? new OuterLargeT(*o.large) : nullptr),
        small(o.small) {
}

inline BadAlignmentRootT &BadAlignmentRootT::operator=(BadAlignmentRootT o) FLATBUFFERS_NOEXCEPT {
  std::swap(large, o.large);
  std::swap(small, o.small);
  return *this;
}

inline BadAlignmentRootT *BadAlignmentRoot::UnPack(const flatbuffers::resolver_function_t *_resolver) const {
  auto _o = std::unique_ptr<BadAlignmentRootT>(new BadAlignmentRootT());
  UnPackTo(_o.get(), _resolver);
  return _o.release();
}

inline void BadAlignmentRoot::UnPackTo(BadAlignmentRootT *_o, const flatbuffers::resolver_function_t *_resolver) const {
  (void)_o;
  (void)_resolver;
  { auto _e = large(); if (_e) { if(_o->large) { _e->UnPackTo(_o->large.get(), _resolver); } else { _o->large = flatbuffers::unique_ptr<OuterLargeT>(_e->UnPack(_resolver)); } } else if (_o->large) { _o->large.reset(); } }
  { auto _e = small(); if (_e) { _o->small.resize(_e->size()); for (flatbuffers::uoffset_t _i = 0; _i < _e->size(); _i++) { _o->small[_i] = *_e->Get(_i); } } else { _o->small.resize(0); } }
}

inline flatbuffers::Offset<BadAlignmentRoot> BadAlignmentRoot::Pack(flatbuffers::FlatBufferBuilder &_fbb, const BadAlignmentRootT* _o, const flatbuffers::rehasher_function_t *_rehasher) {
  return CreateBadAlignmentRoot(_fbb, _o, _rehasher);
}

inline flatbuffers::Offset<BadAlignmentRoot> CreateBadAlignmentRoot(flatbuffers::FlatBufferBuilder &_fbb, const BadAlignmentRootT *_o, const flatbuffers::rehasher_function_t *_rehasher) {
  (void)_rehasher;
  (void)_o;
  struct _VectorArgs { flatbuffers::FlatBufferBuilder *__fbb; const BadAlignmentRootT* __o; const flatbuffers::rehasher_function_t *__rehasher; } _va = { &_fbb, _o, _rehasher}; (void)_va;
  auto _large = _o->large ? CreateOuterLarge(_fbb, _o->large.get(), _rehasher) : 0;
  auto _small = _o->small.size() ? _fbb.CreateVectorOfStructs(_o->small) : 0;
  return CreateBadAlignmentRoot(
      _fbb,
      _large,
      _small);
}

inline const flatbuffers::TypeTable *BadAlignmentSmallTypeTable() {
  static const flatbuffers::TypeCode type_codes[] = {
    { flatbuffers::ET_UINT, 0, -1 },
    { flatbuffers::ET_UINT, 0, -1 },
    { flatbuffers::ET_UINT, 0, -1 }
  };
  static const int64_t values[] = { 0, 4, 8, 12 };
  static const char * const names[] = {
    "var_0",
    "var_1",
    "var_2"
  };
  static const flatbuffers::TypeTable tt = {
    flatbuffers::ST_STRUCT, 3, type_codes, nullptr, nullptr, values, names
  };
  return &tt;
}

inline const flatbuffers::TypeTable *BadAlignmentLargeTypeTable() {
  static const flatbuffers::TypeCode type_codes[] = {
    { flatbuffers::ET_ULONG, 0, -1 }
  };
  static const int64_t values[] = { 0, 8 };
  static const char * const names[] = {
    "var_0"
  };
  static const flatbuffers::TypeTable tt = {
    flatbuffers::ST_STRUCT, 1, type_codes, nullptr, nullptr, values, names
  };
  return &tt;
}

inline const flatbuffers::TypeTable *OuterLargeTypeTable() {
  static const flatbuffers::TypeCode type_codes[] = {
    { flatbuffers::ET_SEQUENCE, 0, 0 }
  };
  static const flatbuffers::TypeFunction type_refs[] = {
    BadAlignmentLargeTypeTable
  };
  static const char * const names[] = {
    "large"
  };
  static const flatbuffers::TypeTable tt = {
    flatbuffers::ST_TABLE, 1, type_codes, type_refs, nullptr, nullptr, names
  };
  return &tt;
}

inline const flatbuffers::TypeTable *BadAlignmentRootTypeTable() {
  static const flatbuffers::TypeCode type_codes[] = {
    { flatbuffers::ET_SEQUENCE, 0, 0 },
    { flatbuffers::ET_SEQUENCE, 1, 1 }
  };
  static const flatbuffers::TypeFunction type_refs[] = {
    OuterLargeTypeTable,
    BadAlignmentSmallTypeTable
  };
  static const char * const names[] = {
    "large",
    "small"
  };
  static const flatbuffers::TypeTable tt = {
    flatbuffers::ST_TABLE, 2, type_codes, type_refs, nullptr, nullptr, names
  };
  return &tt;
}

inline const BadAlignmentRoot *GetBadAlignmentRoot(const void *buf) {
  return flatbuffers::GetRoot<BadAlignmentRoot>(buf);
}

inline const BadAlignmentRoot *GetSizePrefixedBadAlignmentRoot(const void *buf) {
  return flatbuffers::GetSizePrefixedRoot<BadAlignmentRoot>(buf);
}

inline BadAlignmentRoot *GetMutableBadAlignmentRoot(void *buf) {
  return flatbuffers::GetMutableRoot<BadAlignmentRoot>(buf);
}

inline BadAlignmentRoot *GetMutableSizePrefixedBadAlignmentRoot(void *buf) {
  return flatbuffers::GetMutableSizePrefixedRoot<BadAlignmentRoot>(buf);
}

inline bool VerifyBadAlignmentRootBuffer(
    flatbuffers::Verifier &verifier) {
  return verifier.VerifyBuffer<BadAlignmentRoot>(nullptr);
}

inline bool VerifySizePrefixedBadAlignmentRootBuffer(
    flatbuffers::Verifier &verifier) {
  return verifier.VerifySizePrefixedBuffer<BadAlignmentRoot>(nullptr);
}

inline void FinishBadAlignmentRootBuffer(
    flatbuffers::FlatBufferBuilder &fbb,
    flatbuffers::Offset<BadAlignmentRoot> root) {
  fbb.Finish(root);
}

inline void FinishSizePrefixedBadAlignmentRootBuffer(
    flatbuffers::FlatBufferBuilder &fbb,
    flatbuffers::Offset<BadAlignmentRoot> root) {
  fbb.FinishSizePrefixed(root);
}

inline flatbuffers::unique_ptr<BadAlignmentRootT> UnPackBadAlignmentRoot(
    const void *buf,
    const flatbuffers::resolver_function_t *res = nullptr) {
  return flatbuffers::unique_ptr<BadAlignmentRootT>(GetBadAlignmentRoot(buf)->UnPack(res));
}

inline flatbuffers::unique_ptr<BadAlignmentRootT> UnPackSizePrefixedBadAlignmentRoot(
    const void *buf,
    const flatbuffers::resolver_function_t *res = nullptr) {
  return flatbuffers::unique_ptr<BadAlignmentRootT>(GetSizePrefixedBadAlignmentRoot(buf)->UnPack(res));
}

#endif  // FLATBUFFERS_GENERATED_ALIGNMENTTEST_H_
