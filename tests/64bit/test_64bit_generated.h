// automatically generated by the FlatBuffers compiler, do not modify


#ifndef FLATBUFFERS_GENERATED_TEST64BIT_H_
#define FLATBUFFERS_GENERATED_TEST64BIT_H_

#include "flatbuffers/flatbuffers.h"

// Ensure the included flatbuffers.h is the same version as when this file was
// generated, otherwise it may not be compatible.
static_assert(FLATBUFFERS_VERSION_MAJOR == 23 &&
              FLATBUFFERS_VERSION_MINOR == 1 &&
              FLATBUFFERS_VERSION_REVISION == 21,
             "Non-compatible flatbuffers version included");

struct RootTable;
struct RootTableBuilder;
struct RootTableT;

bool operator==(const RootTableT &lhs, const RootTableT &rhs);
bool operator!=(const RootTableT &lhs, const RootTableT &rhs);

inline const ::flatbuffers::TypeTable *RootTableTypeTable();

struct RootTableT : public ::flatbuffers::NativeTable {
  typedef RootTable TableType;
  std::vector<uint8_t> big_vector{};
  int32_t a = 0;
};

struct RootTable FLATBUFFERS_FINAL_CLASS : private ::flatbuffers::Table {
  typedef RootTableT NativeTableType;
  typedef RootTableBuilder Builder;
  static const ::flatbuffers::TypeTable *MiniReflectTypeTable() {
    return RootTableTypeTable();
  }
  enum FlatBuffersVTableOffset FLATBUFFERS_VTABLE_UNDERLYING_TYPE {
    VT_BIG_VECTOR = 4,
    VT_A = 6
  };
  const ::flatbuffers::Vector<uint8_t> *big_vector() const {
    return GetPointer<const ::flatbuffers::Vector<uint8_t> *>(VT_BIG_VECTOR);
  }
  ::flatbuffers::Vector<uint8_t> *mutable_big_vector() {
    return GetPointer<::flatbuffers::Vector<uint8_t> *>(VT_BIG_VECTOR);
  }
  int32_t a() const {
    return GetField<int32_t>(VT_A, 0);
  }
  bool mutate_a(int32_t _a = 0) {
    return SetField<int32_t>(VT_A, _a, 0);
  }
  bool Verify(::flatbuffers::Verifier &verifier) const {
    return VerifyTableStart(verifier) &&
           VerifyOffset(verifier, VT_BIG_VECTOR) &&
           verifier.VerifyVector(big_vector()) &&
           VerifyField<int32_t>(verifier, VT_A, 4) &&
           verifier.EndTable();
  }
  RootTableT *UnPack(const ::flatbuffers::resolver_function_t *_resolver = nullptr) const;
  void UnPackTo(RootTableT *_o, const ::flatbuffers::resolver_function_t *_resolver = nullptr) const;
  static ::flatbuffers::Offset<RootTable> Pack(::flatbuffers::FlatBufferBuilder &_fbb, const RootTableT* _o, const ::flatbuffers::rehasher_function_t *_rehasher = nullptr);
};

struct RootTableBuilder {
  typedef RootTable Table;
  ::flatbuffers::FlatBufferBuilder &fbb_;
  ::flatbuffers::uoffset_t start_;
  void add_big_vector(::flatbuffers::Offset64<::flatbuffers::Vector<uint8_t>> big_vector) {
    fbb_.AddOffset(RootTable::VT_BIG_VECTOR, big_vector);
  }
  void add_a(int32_t a) {
    fbb_.AddElement<int32_t>(RootTable::VT_A, a, 0);
  }
  explicit RootTableBuilder(::flatbuffers::FlatBufferBuilder &_fbb)
        : fbb_(_fbb) {
    start_ = fbb_.StartTable();
  }
  ::flatbuffers::Offset<RootTable> Finish() {
    const auto end = fbb_.EndTable(start_);
    auto o = ::flatbuffers::Offset<RootTable>(end);
    return o;
  }
};

inline ::flatbuffers::Offset<RootTable> CreateRootTable(
    ::flatbuffers::FlatBufferBuilder &_fbb,
    ::flatbuffers::Offset64<::flatbuffers::Vector<uint8_t>> big_vector = 0,
    int32_t a = 0) {
  RootTableBuilder builder_(_fbb);
  builder_.add_a(a);
  builder_.add_big_vector(big_vector);
  return builder_.Finish();
}

inline ::flatbuffers::Offset<RootTable> CreateRootTableDirect(
    ::flatbuffers::FlatBufferBuilder &_fbb,
    const std::vector<uint8_t> *big_vector = nullptr,
    int32_t a = 0) {
  auto big_vector__ = big_vector ? _fbb.CreateVector64<uint8_t>(*big_vector) : 0;
  return CreateRootTable(
      _fbb,
      big_vector__,
      a);
}

::flatbuffers::Offset<RootTable> CreateRootTable(::flatbuffers::FlatBufferBuilder &_fbb, const RootTableT *_o, const ::flatbuffers::rehasher_function_t *_rehasher = nullptr);


inline bool operator==(const RootTableT &lhs, const RootTableT &rhs) {
  return
      (lhs.big_vector == rhs.big_vector) &&
      (lhs.a == rhs.a);
}

inline bool operator!=(const RootTableT &lhs, const RootTableT &rhs) {
    return !(lhs == rhs);
}


inline RootTableT *RootTable::UnPack(const ::flatbuffers::resolver_function_t *_resolver) const {
  auto _o = std::unique_ptr<RootTableT>(new RootTableT());
  UnPackTo(_o.get(), _resolver);
  return _o.release();
}

inline void RootTable::UnPackTo(RootTableT *_o, const ::flatbuffers::resolver_function_t *_resolver) const {
  (void)_o;
  (void)_resolver;
  { auto _e = big_vector(); if (_e) { _o->big_vector.resize(_e->size()); std::copy(_e->begin(), _e->end(), _o->big_vector.begin()); } }
  { auto _e = a(); _o->a = _e; }
}

inline ::flatbuffers::Offset<RootTable> RootTable::Pack(::flatbuffers::FlatBufferBuilder &_fbb, const RootTableT* _o, const ::flatbuffers::rehasher_function_t *_rehasher) {
  return CreateRootTable(_fbb, _o, _rehasher);
}

inline ::flatbuffers::Offset<RootTable> CreateRootTable(::flatbuffers::FlatBufferBuilder &_fbb, const RootTableT *_o, const ::flatbuffers::rehasher_function_t *_rehasher) {
  (void)_rehasher;
  (void)_o;
  struct _VectorArgs { ::flatbuffers::FlatBufferBuilder *__fbb; const RootTableT* __o; const ::flatbuffers::rehasher_function_t *__rehasher; } _va = { &_fbb, _o, _rehasher}; (void)_va;
  auto _big_vector = _o->big_vector.size() ? _fbb.CreateVector64(_o->big_vector) : 0;
  auto _a = _o->a;
  return CreateRootTable(
      _fbb,
      _big_vector,
      _a);
}

inline const ::flatbuffers::TypeTable *RootTableTypeTable() {
  static const ::flatbuffers::TypeCode type_codes[] = {
    { ::flatbuffers::ET_UCHAR, 1, -1 },
    { ::flatbuffers::ET_INT, 0, -1 }
  };
  static const char * const names[] = {
    "big_vector",
    "a"
  };
  static const ::flatbuffers::TypeTable tt = {
    ::flatbuffers::ST_TABLE, 2, type_codes, nullptr, nullptr, nullptr, names
  };
  return &tt;
}

inline const RootTable *GetRootTable(const void *buf) {
  return ::flatbuffers::GetRoot<RootTable>(buf);
}

inline const RootTable *GetSizePrefixedRootTable(const void *buf) {
  return ::flatbuffers::GetSizePrefixedRoot<RootTable>(buf);
}

inline RootTable *GetMutableRootTable(void *buf) {
  return ::flatbuffers::GetMutableRoot<RootTable>(buf);
}

inline RootTable *GetMutableSizePrefixedRootTable(void *buf) {
  return ::flatbuffers::GetMutableSizePrefixedRoot<RootTable>(buf);
}

inline bool VerifyRootTableBuffer(
    ::flatbuffers::Verifier &verifier) {
  return verifier.VerifyBuffer<RootTable>(nullptr);
}

inline bool VerifySizePrefixedRootTableBuffer(
    ::flatbuffers::Verifier &verifier) {
  return verifier.VerifySizePrefixedBuffer<RootTable>(nullptr);
}

inline void FinishRootTableBuffer(
    ::flatbuffers::FlatBufferBuilder &fbb,
    ::flatbuffers::Offset<RootTable> root) {
  fbb.Finish(root);
}

inline void FinishSizePrefixedRootTableBuffer(
    ::flatbuffers::FlatBufferBuilder &fbb,
    ::flatbuffers::Offset<RootTable> root) {
  fbb.FinishSizePrefixed(root);
}

inline flatbuffers::unique_ptr<RootTableT> UnPackRootTable(
    const void *buf,
    const ::flatbuffers::resolver_function_t *res = nullptr) {
  return flatbuffers::unique_ptr<RootTableT>(GetRootTable(buf)->UnPack(res));
}

inline flatbuffers::unique_ptr<RootTableT> UnPackSizePrefixedRootTable(
    const void *buf,
    const ::flatbuffers::resolver_function_t *res = nullptr) {
  return flatbuffers::unique_ptr<RootTableT>(GetSizePrefixedRootTable(buf)->UnPack(res));
}

#endif  // FLATBUFFERS_GENERATED_TEST64BIT_H_
