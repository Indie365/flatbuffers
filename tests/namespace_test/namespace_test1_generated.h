// automatically generated by the FlatBuffers compiler, do not modify


#ifndef FLATBUFFERS_GENERATED_NAMESPACETEST1_NAMESPACEA_NAMESPACEB_H_
#define FLATBUFFERS_GENERATED_NAMESPACETEST1_NAMESPACEA_NAMESPACEB_H_

#include "flatbuffers/flatbuffers.h"
#include "flatbuffers/flatbuffer_builder.h"

namespace NamespaceA {
namespace NamespaceB {

struct TableInNestedNS;
struct TableInNestedNSBuilder;
struct TableInNestedNST;

struct StructInNestedNS;

bool operator==(const TableInNestedNST &lhs, const TableInNestedNST &rhs);
bool operator!=(const TableInNestedNST &lhs, const TableInNestedNST &rhs);
bool operator==(const StructInNestedNS &lhs, const StructInNestedNS &rhs);
bool operator!=(const StructInNestedNS &lhs, const StructInNestedNS &rhs);

inline const flatbuffers::TypeTable *TableInNestedNSTypeTable();

inline const flatbuffers::TypeTable *StructInNestedNSTypeTable();

enum UnionInNestedNS : uint8_t {
  UnionInNestedNS_NONE = 0,
  UnionInNestedNS_TableInNestedNS = 1,
  UnionInNestedNS_MIN = UnionInNestedNS_NONE,
  UnionInNestedNS_MAX = UnionInNestedNS_TableInNestedNS
};

inline const UnionInNestedNS (&EnumValuesUnionInNestedNS())[2] {
  static const UnionInNestedNS values[] = {
    UnionInNestedNS_NONE,
    UnionInNestedNS_TableInNestedNS
  };
  return values;
}

inline const char * const *EnumNamesUnionInNestedNS() {
  static const char * const names[3] = {
    "NONE",
    "TableInNestedNS",
    nullptr
  };
  return names;
}

inline const char *EnumNameUnionInNestedNS(UnionInNestedNS e) {
  if (flatbuffers::IsOutRange(e, UnionInNestedNS_NONE, UnionInNestedNS_TableInNestedNS)) return "";
  const size_t index = static_cast<size_t>(e);
  return EnumNamesUnionInNestedNS()[index];
}

template<typename T> struct UnionInNestedNSTraits {
  static const UnionInNestedNS enum_value = UnionInNestedNS_NONE;
};

template<> struct UnionInNestedNSTraits<NamespaceA::NamespaceB::TableInNestedNS> {
  static const UnionInNestedNS enum_value = UnionInNestedNS_TableInNestedNS;
};

template<typename T> struct UnionInNestedNSUnionTraits {
  static const UnionInNestedNS enum_value = UnionInNestedNS_NONE;
};

template<> struct UnionInNestedNSUnionTraits<NamespaceA::NamespaceB::TableInNestedNST> {
  static const UnionInNestedNS enum_value = UnionInNestedNS_TableInNestedNS;
};

struct UnionInNestedNSUnion {
  UnionInNestedNS type;
  void *value;

  UnionInNestedNSUnion() : type(UnionInNestedNS_NONE), value(nullptr) {}
  UnionInNestedNSUnion(UnionInNestedNSUnion&& u) FLATBUFFERS_NOEXCEPT :
    type(UnionInNestedNS_NONE), value(nullptr)
    { std::swap(type, u.type); std::swap(value, u.value); }
  UnionInNestedNSUnion(const UnionInNestedNSUnion &);
  UnionInNestedNSUnion &operator=(const UnionInNestedNSUnion &u)
    { UnionInNestedNSUnion t(u); std::swap(type, t.type); std::swap(value, t.value); return *this; }
  UnionInNestedNSUnion &operator=(UnionInNestedNSUnion &&u) FLATBUFFERS_NOEXCEPT
    { std::swap(type, u.type); std::swap(value, u.value); return *this; }
  ~UnionInNestedNSUnion() { Reset(); }

  void Reset();

  template <typename T>
  void Set(T&& val) {
    typedef typename std::remove_reference<T>::type RT;
    Reset();
    type = UnionInNestedNSUnionTraits<RT>::enum_value;
    if (type != UnionInNestedNS_NONE) {
      value = new RT(std::forward<T>(val));
    }
  }

  static void *UnPack(const void *obj, UnionInNestedNS type, const flatbuffers::resolver_function_t *resolver);
  flatbuffers::Offset<void> Pack(flatbuffers::FlatBufferBuilder &_fbb, const flatbuffers::rehasher_function_t *_rehasher = nullptr) const;

  NamespaceA::NamespaceB::TableInNestedNST *AsTableInNestedNS() {
    return type == UnionInNestedNS_TableInNestedNS ?
      reinterpret_cast<NamespaceA::NamespaceB::TableInNestedNST *>(value) : nullptr;
  }
  const NamespaceA::NamespaceB::TableInNestedNST *AsTableInNestedNS() const {
    return type == UnionInNestedNS_TableInNestedNS ?
      reinterpret_cast<const NamespaceA::NamespaceB::TableInNestedNST *>(value) : nullptr;
  }
};


inline bool operator==(const UnionInNestedNSUnion &lhs, const UnionInNestedNSUnion &rhs) {
  if (lhs.type != rhs.type) return false;
  switch (lhs.type) {
    case UnionInNestedNS_NONE: {
      return true;
    }
    case UnionInNestedNS_TableInNestedNS: {
      return *(reinterpret_cast<const NamespaceA::NamespaceB::TableInNestedNST *>(lhs.value)) ==
             *(reinterpret_cast<const NamespaceA::NamespaceB::TableInNestedNST *>(rhs.value));
    }
    default: {
      return false;
    }
  }
}

inline bool operator!=(const UnionInNestedNSUnion &lhs, const UnionInNestedNSUnion &rhs) {
    return !(lhs == rhs);
}

bool VerifyUnionInNestedNS(flatbuffers::Verifier &verifier, const void *obj, UnionInNestedNS type);
bool VerifyUnionInNestedNSVector(flatbuffers::Verifier &verifier, const flatbuffers::Vector<flatbuffers::Offset<void>> *values, const flatbuffers::Vector<uint8_t> *types);

enum EnumInNestedNS : int8_t {
  EnumInNestedNS_A = 0,
  EnumInNestedNS_B = 1,
  EnumInNestedNS_C = 2,
  EnumInNestedNS_MIN = EnumInNestedNS_A,
  EnumInNestedNS_MAX = EnumInNestedNS_C
};

inline const EnumInNestedNS (&EnumValuesEnumInNestedNS())[3] {
  static const EnumInNestedNS values[] = {
    EnumInNestedNS_A,
    EnumInNestedNS_B,
    EnumInNestedNS_C
  };
  return values;
}

inline const char * const *EnumNamesEnumInNestedNS() {
  static const char * const names[4] = {
    "A",
    "B",
    "C",
    nullptr
  };
  return names;
}

inline const char *EnumNameEnumInNestedNS(EnumInNestedNS e) {
  if (flatbuffers::IsOutRange(e, EnumInNestedNS_A, EnumInNestedNS_C)) return "";
  const size_t index = static_cast<size_t>(e);
  return EnumNamesEnumInNestedNS()[index];
}

FLATBUFFERS_MANUALLY_ALIGNED_STRUCT(4) StructInNestedNS FLATBUFFERS_FINAL_CLASS {
 private:
  int32_t a_;
  int32_t b_;

 public:
  static const flatbuffers::TypeTable *MiniReflectTypeTable() {
    return StructInNestedNSTypeTable();
  }
  static FLATBUFFERS_CONSTEXPR_CPP11 const char *GetFullyQualifiedName() {
    return "NamespaceA.NamespaceB.StructInNestedNS";
  }
  StructInNestedNS()
      : a_(0),
        b_(0) {
  }
  StructInNestedNS(int32_t _a, int32_t _b)
      : a_(flatbuffers::EndianScalar(_a)),
        b_(flatbuffers::EndianScalar(_b)) {
  }
  int32_t a() const {
    return flatbuffers::EndianScalar(a_);
  }
  void mutate_a(int32_t _a) {
    flatbuffers::WriteScalar(&a_, _a);
  }
  int32_t b() const {
    return flatbuffers::EndianScalar(b_);
  }
  void mutate_b(int32_t _b) {
    flatbuffers::WriteScalar(&b_, _b);
  }
};
FLATBUFFERS_STRUCT_END(StructInNestedNS, 8);

inline bool operator==(const StructInNestedNS &lhs, const StructInNestedNS &rhs) {
  return
      (lhs.a() == rhs.a()) &&
      (lhs.b() == rhs.b());
}

inline bool operator!=(const StructInNestedNS &lhs, const StructInNestedNS &rhs) {
    return !(lhs == rhs);
}


struct TableInNestedNST : public flatbuffers::NativeTable {
  typedef TableInNestedNS TableType;
  static FLATBUFFERS_CONSTEXPR_CPP11 const char *GetFullyQualifiedName() {
    return "NamespaceA.NamespaceB.TableInNestedNST";
  }
  int32_t foo = 0;
};

struct TableInNestedNS FLATBUFFERS_FINAL_CLASS : private flatbuffers::Table {
  typedef TableInNestedNST NativeTableType;
  typedef TableInNestedNSBuilder Builder;
  static const flatbuffers::TypeTable *MiniReflectTypeTable() {
    return TableInNestedNSTypeTable();
  }
  static FLATBUFFERS_CONSTEXPR_CPP11 const char *GetFullyQualifiedName() {
    return "NamespaceA.NamespaceB.TableInNestedNS";
  }
  enum FlatBuffersVTableOffset FLATBUFFERS_VTABLE_UNDERLYING_TYPE {
    VT_FOO = 4
  };
  int32_t foo() const {
    return GetField<int32_t>(VT_FOO, 0);
  }
  bool mutate_foo(int32_t _foo = 0) {
    return SetField<int32_t>(VT_FOO, _foo, 0);
  }
  bool Verify(flatbuffers::Verifier &verifier) const {
    return VerifyTableStart(verifier) &&
           VerifyField<int32_t>(verifier, VT_FOO, 4) &&
           verifier.EndTable();
  }
  TableInNestedNST *UnPack(const flatbuffers::resolver_function_t *_resolver = nullptr) const;
  void UnPackTo(TableInNestedNST *_o, const flatbuffers::resolver_function_t *_resolver = nullptr) const;
  static flatbuffers::Offset<TableInNestedNS> Pack(flatbuffers::FlatBufferBuilder &_fbb, const TableInNestedNST* _o, const flatbuffers::rehasher_function_t *_rehasher = nullptr);
};

struct TableInNestedNSBuilder {
  typedef TableInNestedNS Table;
  flatbuffers::FlatBufferBuilder &fbb_;
  flatbuffers::uoffset_t start_;
  void add_foo(int32_t foo) {
    fbb_.AddElement<int32_t>(TableInNestedNS::VT_FOO, foo, 0);
  }
  explicit TableInNestedNSBuilder(flatbuffers::FlatBufferBuilder &_fbb)
        : fbb_(_fbb) {
    start_ = fbb_.StartTable();
  }
  flatbuffers::Offset<TableInNestedNS> Finish() {
    const auto end = fbb_.EndTable(start_);
    auto o = flatbuffers::Offset<TableInNestedNS>(end);
    return o;
  }
};

inline flatbuffers::Offset<TableInNestedNS> CreateTableInNestedNS(
    flatbuffers::FlatBufferBuilder &_fbb,
    int32_t foo = 0) {
  TableInNestedNSBuilder builder_(_fbb);
  builder_.add_foo(foo);
  return builder_.Finish();
}

flatbuffers::Offset<TableInNestedNS> CreateTableInNestedNS(flatbuffers::FlatBufferBuilder &_fbb, const TableInNestedNST *_o, const flatbuffers::rehasher_function_t *_rehasher = nullptr);


inline bool operator==(const TableInNestedNST &lhs, const TableInNestedNST &rhs) {
  return
      (lhs.foo == rhs.foo);
}

inline bool operator!=(const TableInNestedNST &lhs, const TableInNestedNST &rhs) {
    return !(lhs == rhs);
}


inline TableInNestedNST *TableInNestedNS::UnPack(const flatbuffers::resolver_function_t *_resolver) const {
  auto _o = std::unique_ptr<TableInNestedNST>(new TableInNestedNST());
  UnPackTo(_o.get(), _resolver);
  return _o.release();
}

inline void TableInNestedNS::UnPackTo(TableInNestedNST *_o, const flatbuffers::resolver_function_t *_resolver) const {
  (void)_o;
  (void)_resolver;
  { auto _e = foo(); _o->foo = _e; }
}

inline flatbuffers::Offset<TableInNestedNS> TableInNestedNS::Pack(flatbuffers::FlatBufferBuilder &_fbb, const TableInNestedNST* _o, const flatbuffers::rehasher_function_t *_rehasher) {
  return CreateTableInNestedNS(_fbb, _o, _rehasher);
}

inline flatbuffers::Offset<TableInNestedNS> CreateTableInNestedNS(flatbuffers::FlatBufferBuilder &_fbb, const TableInNestedNST *_o, const flatbuffers::rehasher_function_t *_rehasher) {
  (void)_rehasher;
  (void)_o;
  struct _VectorArgs { flatbuffers::FlatBufferBuilder *__fbb; const TableInNestedNST* __o; const flatbuffers::rehasher_function_t *__rehasher; } _va = { &_fbb, _o, _rehasher}; (void)_va;
  auto _foo = _o->foo;
  return NamespaceA::NamespaceB::CreateTableInNestedNS(
      _fbb,
      _foo);
}

inline bool VerifyUnionInNestedNS(flatbuffers::Verifier &verifier, const void *obj, UnionInNestedNS type) {
  switch (type) {
    case UnionInNestedNS_NONE: {
      return true;
    }
    case UnionInNestedNS_TableInNestedNS: {
      auto ptr = reinterpret_cast<const NamespaceA::NamespaceB::TableInNestedNS *>(obj);
      return verifier.VerifyTable(ptr);
    }
    default: return true;
  }
}

inline bool VerifyUnionInNestedNSVector(flatbuffers::Verifier &verifier, const flatbuffers::Vector<flatbuffers::Offset<void>> *values, const flatbuffers::Vector<uint8_t> *types) {
  if (!values || !types) return !values && !types;
  if (values->size() != types->size()) return false;
  for (flatbuffers::uoffset_t i = 0; i < values->size(); ++i) {
    if (!VerifyUnionInNestedNS(
        verifier,  values->Get(i), types->GetEnum<UnionInNestedNS>(i))) {
      return false;
    }
  }
  return true;
}

inline void *UnionInNestedNSUnion::UnPack(const void *obj, UnionInNestedNS type, const flatbuffers::resolver_function_t *resolver) {
  (void)resolver;
  switch (type) {
    case UnionInNestedNS_TableInNestedNS: {
      auto ptr = reinterpret_cast<const NamespaceA::NamespaceB::TableInNestedNS *>(obj);
      return ptr->UnPack(resolver);
    }
    default: return nullptr;
  }
}

inline flatbuffers::Offset<void> UnionInNestedNSUnion::Pack(flatbuffers::FlatBufferBuilder &_fbb, const flatbuffers::rehasher_function_t *_rehasher) const {
  (void)_rehasher;
  switch (type) {
    case UnionInNestedNS_TableInNestedNS: {
      auto ptr = reinterpret_cast<const NamespaceA::NamespaceB::TableInNestedNST *>(value);
      return CreateTableInNestedNS(_fbb, ptr, _rehasher).Union();
    }
    default: return 0;
  }
}

inline UnionInNestedNSUnion::UnionInNestedNSUnion(const UnionInNestedNSUnion &u) : type(u.type), value(nullptr) {
  switch (type) {
    case UnionInNestedNS_TableInNestedNS: {
      value = new NamespaceA::NamespaceB::TableInNestedNST(*reinterpret_cast<NamespaceA::NamespaceB::TableInNestedNST *>(u.value));
      break;
    }
    default:
      break;
  }
}

inline void UnionInNestedNSUnion::Reset() {
  switch (type) {
    case UnionInNestedNS_TableInNestedNS: {
      auto ptr = reinterpret_cast<NamespaceA::NamespaceB::TableInNestedNST *>(value);
      delete ptr;
      break;
    }
    default: break;
  }
  value = nullptr;
  type = UnionInNestedNS_NONE;
}

inline const flatbuffers::TypeTable *UnionInNestedNSTypeTable() {
  static const flatbuffers::TypeCode type_codes[] = {
    { flatbuffers::ET_SEQUENCE, 0, -1 },
    { flatbuffers::ET_SEQUENCE, 0, 0 }
  };
  static const flatbuffers::TypeFunction type_refs[] = {
    NamespaceA::NamespaceB::TableInNestedNSTypeTable
  };
  static const char * const names[] = {
    "NONE",
    "TableInNestedNS"
  };
  static const flatbuffers::TypeTable tt = {
    flatbuffers::ST_UNION, 2, type_codes, type_refs, nullptr, nullptr, names
  };
  return &tt;
}

inline const flatbuffers::TypeTable *EnumInNestedNSTypeTable() {
  static const flatbuffers::TypeCode type_codes[] = {
    { flatbuffers::ET_CHAR, 0, 0 },
    { flatbuffers::ET_CHAR, 0, 0 },
    { flatbuffers::ET_CHAR, 0, 0 }
  };
  static const flatbuffers::TypeFunction type_refs[] = {
    NamespaceA::NamespaceB::EnumInNestedNSTypeTable
  };
  static const char * const names[] = {
    "A",
    "B",
    "C"
  };
  static const flatbuffers::TypeTable tt = {
    flatbuffers::ST_ENUM, 3, type_codes, type_refs, nullptr, nullptr, names
  };
  return &tt;
}

inline const flatbuffers::TypeTable *TableInNestedNSTypeTable() {
  static const flatbuffers::TypeCode type_codes[] = {
    { flatbuffers::ET_INT, 0, -1 }
  };
  static const char * const names[] = {
    "foo"
  };
  static const flatbuffers::TypeTable tt = {
    flatbuffers::ST_TABLE, 1, type_codes, nullptr, nullptr, nullptr, names
  };
  return &tt;
}

inline const flatbuffers::TypeTable *StructInNestedNSTypeTable() {
  static const flatbuffers::TypeCode type_codes[] = {
    { flatbuffers::ET_INT, 0, -1 },
    { flatbuffers::ET_INT, 0, -1 }
  };
  static const int64_t values[] = { 0, 4, 8 };
  static const char * const names[] = {
    "a",
    "b"
  };
  static const flatbuffers::TypeTable tt = {
    flatbuffers::ST_STRUCT, 2, type_codes, nullptr, nullptr, values, names
  };
  return &tt;
}

}  // namespace NamespaceB
}  // namespace NamespaceA

#endif  // FLATBUFFERS_GENERATED_NAMESPACETEST1_NAMESPACEA_NAMESPACEB_H_
