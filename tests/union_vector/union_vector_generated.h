// automatically generated by the FlatBuffers compiler, do not modify


#ifndef FLATBUFFERS_GENERATED_UNIONVECTOR_H_
#define FLATBUFFERS_GENERATED_UNIONVECTOR_H_

#include "flatbuffers/flatbuffers.h"

struct Attacker;
struct AttackerBuilder;
struct AttackerT;

struct Rapunzel;

struct BookReader;

struct Movie;
struct MovieBuilder;
struct MovieT;

bool operator==(const AttackerT &lhs, const AttackerT &rhs);
bool operator!=(const AttackerT &lhs, const AttackerT &rhs);
bool operator==(const Rapunzel &lhs, const Rapunzel &rhs);
bool operator!=(const Rapunzel &lhs, const Rapunzel &rhs);
bool operator==(const BookReader &lhs, const BookReader &rhs);
bool operator!=(const BookReader &lhs, const BookReader &rhs);
bool operator==(const MovieT &lhs, const MovieT &rhs);
bool operator!=(const MovieT &lhs, const MovieT &rhs);

inline const flatbuffers::TypeTable *AttackerTypeTable();

inline const flatbuffers::TypeTable *RapunzelTypeTable();

inline const flatbuffers::TypeTable *BookReaderTypeTable();

inline const flatbuffers::TypeTable *MovieTypeTable();

enum Character {
  Character_NONE = 0,
  Character_MuLan = 1,
  Character_Rapunzel = 2,
  Character_Belle = 3,
  Character_BookFan = 4,
  Character_Other = 5,
  Character_Unused = 6,
  Character_MIN = Character_NONE,
  Character_MAX = Character_Unused
};

inline const Character (&EnumValuesCharacter())[7] {
  static const Character values[] = {
    Character_NONE,
    Character_MuLan,
    Character_Rapunzel,
    Character_Belle,
    Character_BookFan,
    Character_Other,
    Character_Unused
  };
  return values;
}

inline const char * const *EnumNamesCharacter() {
  static const char * const names[8] = {
    "NONE",
    "MuLan",
    "Rapunzel",
    "Belle",
    "BookFan",
    "Other",
    "Unused",
    nullptr
  };
  return names;
}

inline const char *EnumNameCharacter(Character e) {
  if (flatbuffers::IsOutRange(e, Character_NONE, Character_Unused)) return "";
  const size_t index = static_cast<size_t>(e);
  return EnumNamesCharacter()[index];
}

struct CharacterUnion {
  Character type;
  void *value;

  CharacterUnion() : type(Character_NONE), value(nullptr) {}
  CharacterUnion(CharacterUnion&& u) FLATBUFFERS_NOEXCEPT :
    type(Character_NONE), value(nullptr)
    { std::swap(type, u.type); std::swap(value, u.value); }
  CharacterUnion(const CharacterUnion &) FLATBUFFERS_NOEXCEPT;
  CharacterUnion &operator=(const CharacterUnion &u) FLATBUFFERS_NOEXCEPT
    { CharacterUnion t(u); std::swap(type, t.type); std::swap(value, t.value); return *this; }
  CharacterUnion &operator=(CharacterUnion &&u) FLATBUFFERS_NOEXCEPT
    { std::swap(type, u.type); std::swap(value, u.value); return *this; }
  ~CharacterUnion() { Reset(); }

  void Reset();

  static void *UnPack(const void *obj, Character type, const flatbuffers::resolver_function_t *resolver);
  flatbuffers::Offset<void> Pack(flatbuffers::FlatBufferBuilder &_fbb, const flatbuffers::rehasher_function_t *_rehasher = nullptr) const;

  AttackerT *AsMuLan() {
    return type == Character_MuLan ?
      reinterpret_cast<AttackerT *>(value) : nullptr;
  }
  const AttackerT *AsMuLan() const {
    return type == Character_MuLan ?
      reinterpret_cast<const AttackerT *>(value) : nullptr;
  }
  Rapunzel *AsRapunzel() {
    return type == Character_Rapunzel ?
      reinterpret_cast<Rapunzel *>(value) : nullptr;
  }
  const Rapunzel *AsRapunzel() const {
    return type == Character_Rapunzel ?
      reinterpret_cast<const Rapunzel *>(value) : nullptr;
  }
  BookReader *AsBelle() {
    return type == Character_Belle ?
      reinterpret_cast<BookReader *>(value) : nullptr;
  }
  const BookReader *AsBelle() const {
    return type == Character_Belle ?
      reinterpret_cast<const BookReader *>(value) : nullptr;
  }
  BookReader *AsBookFan() {
    return type == Character_BookFan ?
      reinterpret_cast<BookReader *>(value) : nullptr;
  }
  const BookReader *AsBookFan() const {
    return type == Character_BookFan ?
      reinterpret_cast<const BookReader *>(value) : nullptr;
  }
  std::string *AsOther() {
    return type == Character_Other ?
      reinterpret_cast<std::string *>(value) : nullptr;
  }
  const std::string *AsOther() const {
    return type == Character_Other ?
      reinterpret_cast<const std::string *>(value) : nullptr;
  }
  std::string *AsUnused() {
    return type == Character_Unused ?
      reinterpret_cast<std::string *>(value) : nullptr;
  }
  const std::string *AsUnused() const {
    return type == Character_Unused ?
      reinterpret_cast<const std::string *>(value) : nullptr;
  }
};


inline bool operator==(const CharacterUnion &lhs, const CharacterUnion &rhs) {
  if (lhs.type != rhs.type) return false;
  switch (lhs.type) {
    case Character_NONE: {
      return true;
    }
    case Character_MuLan: {
      return *(reinterpret_cast<const AttackerT *>(lhs.value)) ==
             *(reinterpret_cast<const AttackerT *>(rhs.value));
    }
    case Character_Rapunzel: {
      return *(reinterpret_cast<const Rapunzel *>(lhs.value)) ==
             *(reinterpret_cast<const Rapunzel *>(rhs.value));
    }
    case Character_Belle: {
      return *(reinterpret_cast<const BookReader *>(lhs.value)) ==
             *(reinterpret_cast<const BookReader *>(rhs.value));
    }
    case Character_BookFan: {
      return *(reinterpret_cast<const BookReader *>(lhs.value)) ==
             *(reinterpret_cast<const BookReader *>(rhs.value));
    }
    case Character_Other: {
      return *(reinterpret_cast<const std::string *>(lhs.value)) ==
             *(reinterpret_cast<const std::string *>(rhs.value));
    }
    case Character_Unused: {
      return *(reinterpret_cast<const std::string *>(lhs.value)) ==
             *(reinterpret_cast<const std::string *>(rhs.value));
    }
    default: {
      return false;
    }
  }
}

inline bool operator!=(const CharacterUnion &lhs, const CharacterUnion &rhs) {
    return !(lhs == rhs);
}

bool VerifyCharacter(flatbuffers::Verifier &verifier, const void *obj, Character type);
bool VerifyCharacterVector(flatbuffers::Verifier &verifier, const flatbuffers::Vector<flatbuffers::Offset<void>> *values, const flatbuffers::Vector<uint8_t> *types);

FLATBUFFERS_MANUALLY_ALIGNED_STRUCT(4) Rapunzel FLATBUFFERS_FINAL_CLASS {
 private:
  int32_t hair_length_;

 public:
  static const flatbuffers::TypeTable *MiniReflectTypeTable() {
    return RapunzelTypeTable();
  }
  static FLATBUFFERS_CONSTEXPR const char *GetFullyQualifiedName() {
    return "Rapunzel";
  }
  Rapunzel() {
    memset(static_cast<void *>(this), 0, sizeof(Rapunzel));
  }
  Rapunzel(int32_t _hair_length)
      : hair_length_(flatbuffers::EndianScalar(_hair_length)) {
  }
  int32_t hair_length() const {
    return flatbuffers::EndianScalar(hair_length_);
  }
  void mutate_hair_length(int32_t _hair_length) {
    flatbuffers::WriteScalar(&hair_length_, _hair_length);
  }
};
FLATBUFFERS_STRUCT_END(Rapunzel, 4);

inline bool operator==(const Rapunzel &lhs, const Rapunzel &rhs) {
  return
      (lhs.hair_length() == rhs.hair_length());
}

inline bool operator!=(const Rapunzel &lhs, const Rapunzel &rhs) {
    return !(lhs == rhs);
}


FLATBUFFERS_MANUALLY_ALIGNED_STRUCT(4) BookReader FLATBUFFERS_FINAL_CLASS {
 private:
  int32_t books_read_;

 public:
  static const flatbuffers::TypeTable *MiniReflectTypeTable() {
    return BookReaderTypeTable();
  }
  static FLATBUFFERS_CONSTEXPR const char *GetFullyQualifiedName() {
    return "BookReader";
  }
  BookReader() {
    memset(static_cast<void *>(this), 0, sizeof(BookReader));
  }
  BookReader(int32_t _books_read)
      : books_read_(flatbuffers::EndianScalar(_books_read)) {
  }
  int32_t books_read() const {
    return flatbuffers::EndianScalar(books_read_);
  }
  void mutate_books_read(int32_t _books_read) {
    flatbuffers::WriteScalar(&books_read_, _books_read);
  }
};
FLATBUFFERS_STRUCT_END(BookReader, 4);

inline bool operator==(const BookReader &lhs, const BookReader &rhs) {
  return
      (lhs.books_read() == rhs.books_read());
}

inline bool operator!=(const BookReader &lhs, const BookReader &rhs) {
    return !(lhs == rhs);
}


struct AttackerT : public flatbuffers::NativeTable {
  typedef Attacker TableType;
  static FLATBUFFERS_CONSTEXPR const char *GetFullyQualifiedName() {
    return "AttackerT";
  }
  int32_t sword_attack_damage;
  AttackerT()
      : sword_attack_damage(0) {
  }
};

inline bool operator==(const AttackerT &lhs, const AttackerT &rhs) {
  return
      (lhs.sword_attack_damage == rhs.sword_attack_damage);
}

inline bool operator!=(const AttackerT &lhs, const AttackerT &rhs) {
    return !(lhs == rhs);
}


struct Attacker FLATBUFFERS_FINAL_CLASS : private flatbuffers::Table {
  typedef AttackerT NativeTableType;
  typedef AttackerBuilder Builder;
  static const flatbuffers::TypeTable *MiniReflectTypeTable() {
    return AttackerTypeTable();
  }
  static FLATBUFFERS_CONSTEXPR const char *GetFullyQualifiedName() {
    return "Attacker";
  }
  enum FlatBuffersVTableOffset FLATBUFFERS_VTABLE_UNDERLYING_TYPE {
    VT_SWORD_ATTACK_DAMAGE = 4
  };
  int32_t sword_attack_damage() const {
    return GetField<int32_t>(VT_SWORD_ATTACK_DAMAGE, 0);
  }
  bool mutate_sword_attack_damage(int32_t _sword_attack_damage) {
    return SetField<int32_t>(VT_SWORD_ATTACK_DAMAGE, _sword_attack_damage, 0);
  }
  bool Verify(flatbuffers::Verifier &verifier) const {
    return VerifyTableStart(verifier) &&
           VerifyField<int32_t>(verifier, VT_SWORD_ATTACK_DAMAGE) &&
           verifier.EndTable();
  }
  AttackerT *UnPack(const flatbuffers::resolver_function_t *_resolver = nullptr) const;
  void UnPackTo(AttackerT *_o, const flatbuffers::resolver_function_t *_resolver = nullptr) const;
  static flatbuffers::Offset<Attacker> Pack(flatbuffers::FlatBufferBuilder &_fbb, const AttackerT* _o, const flatbuffers::rehasher_function_t *_rehasher = nullptr);
};

struct AttackerBuilder {
  typedef Attacker Table;
  flatbuffers::FlatBufferBuilder &fbb_;
  flatbuffers::uoffset_t start_;
  void add_sword_attack_damage(int32_t sword_attack_damage) {
    fbb_.AddElement<int32_t>(Attacker::VT_SWORD_ATTACK_DAMAGE, sword_attack_damage, 0);
  }
  explicit AttackerBuilder(flatbuffers::FlatBufferBuilder &_fbb)
        : fbb_(_fbb) {
    start_ = fbb_.StartTable();
  }
  AttackerBuilder &operator=(const AttackerBuilder &);
  flatbuffers::Offset<Attacker> Finish() {
    const auto end = fbb_.EndTable(start_);
    auto o = flatbuffers::Offset<Attacker>(end);
    return o;
  }
};

inline flatbuffers::Offset<Attacker> CreateAttacker(
    flatbuffers::FlatBufferBuilder &_fbb,
    int32_t sword_attack_damage = 0) {
  AttackerBuilder builder_(_fbb);
  builder_.add_sword_attack_damage(sword_attack_damage);
  return builder_.Finish();
}

flatbuffers::Offset<Attacker> CreateAttacker(flatbuffers::FlatBufferBuilder &_fbb, const AttackerT *_o, const flatbuffers::rehasher_function_t *_rehasher = nullptr);

struct MovieT : public flatbuffers::NativeTable {
  typedef Movie TableType;
  static FLATBUFFERS_CONSTEXPR const char *GetFullyQualifiedName() {
    return "MovieT";
  }
  CharacterUnion main_character;
  std::vector<CharacterUnion> characters;
  MovieT() {
  }
};

inline bool operator==(const MovieT &lhs, const MovieT &rhs) {
  return
      (lhs.main_character == rhs.main_character) &&
      (lhs.characters == rhs.characters);
}

inline bool operator!=(const MovieT &lhs, const MovieT &rhs) {
    return !(lhs == rhs);
}


struct Movie FLATBUFFERS_FINAL_CLASS : private flatbuffers::Table {
  typedef MovieT NativeTableType;
  typedef MovieBuilder Builder;
  static const flatbuffers::TypeTable *MiniReflectTypeTable() {
    return MovieTypeTable();
  }
  static FLATBUFFERS_CONSTEXPR const char *GetFullyQualifiedName() {
    return "Movie";
  }
  enum FlatBuffersVTableOffset FLATBUFFERS_VTABLE_UNDERLYING_TYPE {
    VT_MAIN_CHARACTER_TYPE = 4,
    VT_MAIN_CHARACTER = 6,
    VT_CHARACTERS_TYPE = 8,
    VT_CHARACTERS = 10
  };
  Character main_character_type() const {
    return static_cast<Character>(GetField<uint8_t>(VT_MAIN_CHARACTER_TYPE, 0));
  }
  const void *main_character() const {
    return GetPointer<const void *>(VT_MAIN_CHARACTER);
  }
  const Attacker *main_character_as_MuLan() const {
    return main_character_type() == Character_MuLan ? static_cast<const Attacker *>(main_character()) : nullptr;
  }
  const Rapunzel *main_character_as_Rapunzel() const {
    return main_character_type() == Character_Rapunzel ? static_cast<const Rapunzel *>(main_character()) : nullptr;
  }
  const BookReader *main_character_as_Belle() const {
    return main_character_type() == Character_Belle ? static_cast<const BookReader *>(main_character()) : nullptr;
  }
  const BookReader *main_character_as_BookFan() const {
    return main_character_type() == Character_BookFan ? static_cast<const BookReader *>(main_character()) : nullptr;
  }
  const flatbuffers::String *main_character_as_Other() const {
    return main_character_type() == Character_Other ? static_cast<const flatbuffers::String *>(main_character()) : nullptr;
  }
  const flatbuffers::String *main_character_as_Unused() const {
    return main_character_type() == Character_Unused ? static_cast<const flatbuffers::String *>(main_character()) : nullptr;
  }
  void *mutable_main_character() {
    return GetPointer<void *>(VT_MAIN_CHARACTER);
  }
  const flatbuffers::Vector<uint8_t> *characters_type() const {
    return GetPointer<const flatbuffers::Vector<uint8_t> *>(VT_CHARACTERS_TYPE);
  }
  flatbuffers::Vector<uint8_t> *mutable_characters_type() {
    return GetPointer<flatbuffers::Vector<uint8_t> *>(VT_CHARACTERS_TYPE);
  }
  const flatbuffers::Vector<flatbuffers::Offset<void>> *characters() const {
    return GetPointer<const flatbuffers::Vector<flatbuffers::Offset<void>> *>(VT_CHARACTERS);
  }
  flatbuffers::Vector<flatbuffers::Offset<void>> *mutable_characters() {
    return GetPointer<flatbuffers::Vector<flatbuffers::Offset<void>> *>(VT_CHARACTERS);
  }
  bool Verify(flatbuffers::Verifier &verifier) const {
    return VerifyTableStart(verifier) &&
           VerifyField<uint8_t>(verifier, VT_MAIN_CHARACTER_TYPE) &&
           VerifyOffset(verifier, VT_MAIN_CHARACTER) &&
           VerifyCharacter(verifier, main_character(), main_character_type()) &&
           VerifyOffset(verifier, VT_CHARACTERS_TYPE) &&
           verifier.VerifyVector(characters_type()) &&
           VerifyOffset(verifier, VT_CHARACTERS) &&
           verifier.VerifyVector(characters()) &&
           VerifyCharacterVector(verifier, characters(), characters_type()) &&
           verifier.EndTable();
  }
  MovieT *UnPack(const flatbuffers::resolver_function_t *_resolver = nullptr) const;
  void UnPackTo(MovieT *_o, const flatbuffers::resolver_function_t *_resolver = nullptr) const;
  static flatbuffers::Offset<Movie> Pack(flatbuffers::FlatBufferBuilder &_fbb, const MovieT* _o, const flatbuffers::rehasher_function_t *_rehasher = nullptr);
};

struct MovieBuilder {
  typedef Movie Table;
  flatbuffers::FlatBufferBuilder &fbb_;
  flatbuffers::uoffset_t start_;
  void add_main_character_type(Character main_character_type) {
    fbb_.AddElement<uint8_t>(Movie::VT_MAIN_CHARACTER_TYPE, static_cast<uint8_t>(main_character_type), 0);
  }
  void add_main_character(flatbuffers::Offset<void> main_character) {
    fbb_.AddOffset(Movie::VT_MAIN_CHARACTER, main_character);
  }
  void add_characters_type(flatbuffers::Offset<flatbuffers::Vector<uint8_t>> characters_type) {
    fbb_.AddOffset(Movie::VT_CHARACTERS_TYPE, characters_type);
  }
  void add_characters(flatbuffers::Offset<flatbuffers::Vector<flatbuffers::Offset<void>>> characters) {
    fbb_.AddOffset(Movie::VT_CHARACTERS, characters);
  }
  explicit MovieBuilder(flatbuffers::FlatBufferBuilder &_fbb)
        : fbb_(_fbb) {
    start_ = fbb_.StartTable();
  }
  MovieBuilder &operator=(const MovieBuilder &);
  flatbuffers::Offset<Movie> Finish() {
    const auto end = fbb_.EndTable(start_);
    auto o = flatbuffers::Offset<Movie>(end);
    return o;
  }
};

inline flatbuffers::Offset<Movie> CreateMovie(
    flatbuffers::FlatBufferBuilder &_fbb,
    Character main_character_type = Character_NONE,
    flatbuffers::Offset<void> main_character = 0,
    flatbuffers::Offset<flatbuffers::Vector<uint8_t>> characters_type = 0,
    flatbuffers::Offset<flatbuffers::Vector<flatbuffers::Offset<void>>> characters = 0) {
  MovieBuilder builder_(_fbb);
  builder_.add_characters(characters);
  builder_.add_characters_type(characters_type);
  builder_.add_main_character(main_character);
  builder_.add_main_character_type(main_character_type);
  return builder_.Finish();
}

inline flatbuffers::Offset<Movie> CreateMovieDirect(
    flatbuffers::FlatBufferBuilder &_fbb,
    Character main_character_type = Character_NONE,
    flatbuffers::Offset<void> main_character = 0,
    const std::vector<uint8_t> *characters_type = nullptr,
    const std::vector<flatbuffers::Offset<void>> *characters = nullptr) {
  auto characters_type__ = characters_type ? _fbb.CreateVector<uint8_t>(*characters_type) : 0;
  auto characters__ = characters ? _fbb.CreateVector<flatbuffers::Offset<void>>(*characters) : 0;
  return CreateMovie(
      _fbb,
      main_character_type,
      main_character,
      characters_type__,
      characters__);
}

flatbuffers::Offset<Movie> CreateMovie(flatbuffers::FlatBufferBuilder &_fbb, const MovieT *_o, const flatbuffers::rehasher_function_t *_rehasher = nullptr);

inline AttackerT *Attacker::UnPack(const flatbuffers::resolver_function_t *_resolver) const {
  auto _o = new AttackerT();
  UnPackTo(_o, _resolver);
  return _o;
}

inline void Attacker::UnPackTo(AttackerT *_o, const flatbuffers::resolver_function_t *_resolver) const {
  (void)_o;
  (void)_resolver;
  { auto _e = sword_attack_damage(); _o->sword_attack_damage = _e; }
}

inline flatbuffers::Offset<Attacker> Attacker::Pack(flatbuffers::FlatBufferBuilder &_fbb, const AttackerT* _o, const flatbuffers::rehasher_function_t *_rehasher) {
  return CreateAttacker(_fbb, _o, _rehasher);
}

inline flatbuffers::Offset<Attacker> CreateAttacker(flatbuffers::FlatBufferBuilder &_fbb, const AttackerT *_o, const flatbuffers::rehasher_function_t *_rehasher) {
  (void)_rehasher;
  (void)_o;
  struct _VectorArgs { flatbuffers::FlatBufferBuilder *__fbb; const AttackerT* __o; const flatbuffers::rehasher_function_t *__rehasher; } _va = { &_fbb, _o, _rehasher}; (void)_va;
  auto _sword_attack_damage = _o->sword_attack_damage;
  return CreateAttacker(
      _fbb,
      _sword_attack_damage);
}

inline MovieT *Movie::UnPack(const flatbuffers::resolver_function_t *_resolver) const {
  auto _o = new MovieT();
  UnPackTo(_o, _resolver);
  return _o;
}

inline void Movie::UnPackTo(MovieT *_o, const flatbuffers::resolver_function_t *_resolver) const {
  (void)_o;
  (void)_resolver;
  { auto _e = main_character_type(); _o->main_character.type = _e; }
  { auto _e = main_character(); if (_e) _o->main_character.value = CharacterUnion::UnPack(_e, main_character_type(), _resolver); }
  { auto _e = characters_type(); if (_e) { _o->characters.resize(_e->size()); for (flatbuffers::uoffset_t _i = 0; _i < _e->size(); _i++) { _o->characters[_i].type = static_cast<Character>(_e->Get(_i)); } } }
  { auto _e = characters(); if (_e) { _o->characters.resize(_e->size()); for (flatbuffers::uoffset_t _i = 0; _i < _e->size(); _i++) { _o->characters[_i].value = CharacterUnion::UnPack(_e->Get(_i), characters_type()->GetEnum<Character>(_i), _resolver); } } }
}

inline flatbuffers::Offset<Movie> Movie::Pack(flatbuffers::FlatBufferBuilder &_fbb, const MovieT* _o, const flatbuffers::rehasher_function_t *_rehasher) {
  return CreateMovie(_fbb, _o, _rehasher);
}

inline flatbuffers::Offset<Movie> CreateMovie(flatbuffers::FlatBufferBuilder &_fbb, const MovieT *_o, const flatbuffers::rehasher_function_t *_rehasher) {
  (void)_rehasher;
  (void)_o;
  struct _VectorArgs { flatbuffers::FlatBufferBuilder *__fbb; const MovieT* __o; const flatbuffers::rehasher_function_t *__rehasher; } _va = { &_fbb, _o, _rehasher}; (void)_va;
  auto _main_character_type = _o->main_character.type;
  auto _main_character = _o->main_character.Pack(_fbb);
  auto _characters_type = _o->characters.size() ? _fbb.CreateVector<uint8_t>(_o->characters.size(), [](size_t i, _VectorArgs *__va) { return static_cast<uint8_t>(__va->__o->characters[i].type); }, &_va) : 0;
  auto _characters = _o->characters.size() ? _fbb.CreateVector<flatbuffers::Offset<void>>(_o->characters.size(), [](size_t i, _VectorArgs *__va) { return __va->__o->characters[i].Pack(*__va->__fbb, __va->__rehasher); }, &_va) : 0;
  return CreateMovie(
      _fbb,
      _main_character_type,
      _main_character,
      _characters_type,
      _characters);
}

inline bool VerifyCharacter(flatbuffers::Verifier &verifier, const void *obj, Character type) {
  switch (type) {
    case Character_NONE: {
      return true;
    }
    case Character_MuLan: {
      auto ptr = reinterpret_cast<const Attacker *>(obj);
      return verifier.VerifyTable(ptr);
    }
    case Character_Rapunzel: {
      return verifier.Verify<Rapunzel>(static_cast<const uint8_t *>(obj), 0);
    }
    case Character_Belle: {
      return verifier.Verify<BookReader>(static_cast<const uint8_t *>(obj), 0);
    }
    case Character_BookFan: {
      return verifier.Verify<BookReader>(static_cast<const uint8_t *>(obj), 0);
    }
    case Character_Other: {
      auto ptr = reinterpret_cast<const flatbuffers::String *>(obj);
      return verifier.VerifyString(ptr);
    }
    case Character_Unused: {
      auto ptr = reinterpret_cast<const flatbuffers::String *>(obj);
      return verifier.VerifyString(ptr);
    }
    default: return true;
  }
}

inline bool VerifyCharacterVector(flatbuffers::Verifier &verifier, const flatbuffers::Vector<flatbuffers::Offset<void>> *values, const flatbuffers::Vector<uint8_t> *types) {
  if (!values || !types) return !values && !types;
  if (values->size() != types->size()) return false;
  for (flatbuffers::uoffset_t i = 0; i < values->size(); ++i) {
    if (!VerifyCharacter(
        verifier,  values->Get(i), types->GetEnum<Character>(i))) {
      return false;
    }
  }
  return true;
}

inline void *CharacterUnion::UnPack(const void *obj, Character type, const flatbuffers::resolver_function_t *resolver) {
  switch (type) {
    case Character_MuLan: {
      auto ptr = reinterpret_cast<const Attacker *>(obj);
      return ptr->UnPack(resolver);
    }
    case Character_Rapunzel: {
      auto ptr = reinterpret_cast<const Rapunzel *>(obj);
      return new Rapunzel(*ptr);
    }
    case Character_Belle: {
      auto ptr = reinterpret_cast<const BookReader *>(obj);
      return new BookReader(*ptr);
    }
    case Character_BookFan: {
      auto ptr = reinterpret_cast<const BookReader *>(obj);
      return new BookReader(*ptr);
    }
    case Character_Other: {
      auto ptr = reinterpret_cast<const flatbuffers::String *>(obj);
      return new std::string(ptr->c_str(), ptr->size());
    }
    case Character_Unused: {
      auto ptr = reinterpret_cast<const flatbuffers::String *>(obj);
      return new std::string(ptr->c_str(), ptr->size());
    }
    default: return nullptr;
  }
}

inline flatbuffers::Offset<void> CharacterUnion::Pack(flatbuffers::FlatBufferBuilder &_fbb, const flatbuffers::rehasher_function_t *_rehasher) const {
  switch (type) {
    case Character_MuLan: {
      auto ptr = reinterpret_cast<const AttackerT *>(value);
      return CreateAttacker(_fbb, ptr, _rehasher).Union();
    }
    case Character_Rapunzel: {
      auto ptr = reinterpret_cast<const Rapunzel *>(value);
      return _fbb.CreateStruct(*ptr).Union();
    }
    case Character_Belle: {
      auto ptr = reinterpret_cast<const BookReader *>(value);
      return _fbb.CreateStruct(*ptr).Union();
    }
    case Character_BookFan: {
      auto ptr = reinterpret_cast<const BookReader *>(value);
      return _fbb.CreateStruct(*ptr).Union();
    }
    case Character_Other: {
      auto ptr = reinterpret_cast<const std::string *>(value);
      return _fbb.CreateString(*ptr).Union();
    }
    case Character_Unused: {
      auto ptr = reinterpret_cast<const std::string *>(value);
      return _fbb.CreateString(*ptr).Union();
    }
    default: return 0;
  }
}

inline CharacterUnion::CharacterUnion(const CharacterUnion &u) FLATBUFFERS_NOEXCEPT : type(u.type), value(nullptr) {
  switch (type) {
    case Character_MuLan: {
      value = new AttackerT(*reinterpret_cast<AttackerT *>(u.value));
      break;
    }
    case Character_Rapunzel: {
      value = new Rapunzel(*reinterpret_cast<Rapunzel *>(u.value));
      break;
    }
    case Character_Belle: {
      value = new BookReader(*reinterpret_cast<BookReader *>(u.value));
      break;
    }
    case Character_BookFan: {
      value = new BookReader(*reinterpret_cast<BookReader *>(u.value));
      break;
    }
    case Character_Other: {
      value = new std::string(*reinterpret_cast<std::string *>(u.value));
      break;
    }
    case Character_Unused: {
      value = new std::string(*reinterpret_cast<std::string *>(u.value));
      break;
    }
    default:
      break;
  }
}

inline void CharacterUnion::Reset() {
  switch (type) {
    case Character_MuLan: {
      auto ptr = reinterpret_cast<AttackerT *>(value);
      delete ptr;
      break;
    }
    case Character_Rapunzel: {
      auto ptr = reinterpret_cast<Rapunzel *>(value);
      delete ptr;
      break;
    }
    case Character_Belle: {
      auto ptr = reinterpret_cast<BookReader *>(value);
      delete ptr;
      break;
    }
    case Character_BookFan: {
      auto ptr = reinterpret_cast<BookReader *>(value);
      delete ptr;
      break;
    }
    case Character_Other: {
      auto ptr = reinterpret_cast<std::string *>(value);
      delete ptr;
      break;
    }
    case Character_Unused: {
      auto ptr = reinterpret_cast<std::string *>(value);
      delete ptr;
      break;
    }
    default: break;
  }
  value = nullptr;
  type = Character_NONE;
}

inline const flatbuffers::TypeTable *CharacterTypeTable() {
  static const flatbuffers::TypeCode type_codes[] = {
    { flatbuffers::ET_SEQUENCE, 0, -1 },
    { flatbuffers::ET_SEQUENCE, 0, 0 },
    { flatbuffers::ET_SEQUENCE, 0, 1 },
    { flatbuffers::ET_SEQUENCE, 0, 2 },
    { flatbuffers::ET_SEQUENCE, 0, 2 },
    { flatbuffers::ET_STRING, 0, -1 },
    { flatbuffers::ET_STRING, 0, -1 }
  };
  static const flatbuffers::TypeFunction type_refs[] = {
    AttackerTypeTable,
    RapunzelTypeTable,
    BookReaderTypeTable
  };
  static const char * const names[] = {
    "NONE",
    "MuLan",
    "Rapunzel",
    "Belle",
    "BookFan",
    "Other",
    "Unused"
  };
  static const flatbuffers::TypeTable tt = {
    flatbuffers::ST_UNION, 7, type_codes, type_refs, nullptr, names
  };
  return &tt;
}

inline const flatbuffers::TypeTable *AttackerTypeTable() {
  static const flatbuffers::TypeCode type_codes[] = {
    { flatbuffers::ET_INT, 0, -1 }
  };
  static const char * const names[] = {
    "sword_attack_damage"
  };
  static const flatbuffers::TypeTable tt = {
    flatbuffers::ST_TABLE, 1, type_codes, nullptr, nullptr, names
  };
  return &tt;
}

inline const flatbuffers::TypeTable *RapunzelTypeTable() {
  static const flatbuffers::TypeCode type_codes[] = {
    { flatbuffers::ET_INT, 0, -1 }
  };
  static const int64_t values[] = { 0, 4 };
  static const char * const names[] = {
    "hair_length"
  };
  static const flatbuffers::TypeTable tt = {
    flatbuffers::ST_STRUCT, 1, type_codes, nullptr, values, names
  };
  return &tt;
}

inline const flatbuffers::TypeTable *BookReaderTypeTable() {
  static const flatbuffers::TypeCode type_codes[] = {
    { flatbuffers::ET_INT, 0, -1 }
  };
  static const int64_t values[] = { 0, 4 };
  static const char * const names[] = {
    "books_read"
  };
  static const flatbuffers::TypeTable tt = {
    flatbuffers::ST_STRUCT, 1, type_codes, nullptr, values, names
  };
  return &tt;
}

inline const flatbuffers::TypeTable *MovieTypeTable() {
  static const flatbuffers::TypeCode type_codes[] = {
    { flatbuffers::ET_UTYPE, 0, 0 },
    { flatbuffers::ET_SEQUENCE, 0, 0 },
    { flatbuffers::ET_UTYPE, 1, 0 },
    { flatbuffers::ET_SEQUENCE, 1, 0 }
  };
  static const flatbuffers::TypeFunction type_refs[] = {
    CharacterTypeTable
  };
  static const char * const names[] = {
    "main_character_type",
    "main_character",
    "characters_type",
    "characters"
  };
  static const flatbuffers::TypeTable tt = {
    flatbuffers::ST_TABLE, 4, type_codes, type_refs, nullptr, names
  };
  return &tt;
}

inline const Movie *GetMovie(const void *buf) {
  return flatbuffers::GetRoot<Movie>(buf);
}

inline const Movie *GetSizePrefixedMovie(const void *buf) {
  return flatbuffers::GetSizePrefixedRoot<Movie>(buf);
}

inline Movie *GetMutableMovie(void *buf) {
  return flatbuffers::GetMutableRoot<Movie>(buf);
}

inline const char *MovieIdentifier() {
  return "MOVI";
}

inline bool MovieBufferHasIdentifier(const void *buf) {
  return flatbuffers::BufferHasIdentifier(
      buf, MovieIdentifier());
}

inline bool VerifyMovieBuffer(
    flatbuffers::Verifier &verifier) {
  return verifier.VerifyBuffer<Movie>(MovieIdentifier());
}

inline bool VerifySizePrefixedMovieBuffer(
    flatbuffers::Verifier &verifier) {
  return verifier.VerifySizePrefixedBuffer<Movie>(MovieIdentifier());
}

inline void FinishMovieBuffer(
    flatbuffers::FlatBufferBuilder &fbb,
    flatbuffers::Offset<Movie> root) {
  fbb.Finish(root, MovieIdentifier());
}

inline void FinishSizePrefixedMovieBuffer(
    flatbuffers::FlatBufferBuilder &fbb,
    flatbuffers::Offset<Movie> root) {
  fbb.FinishSizePrefixed(root, MovieIdentifier());
}

inline flatbuffers::unique_ptr<MovieT> UnPackMovie(
    const void *buf,
    const flatbuffers::resolver_function_t *res = nullptr) {
  return flatbuffers::unique_ptr<MovieT>(GetMovie(buf)->UnPack(res));
}

inline flatbuffers::unique_ptr<MovieT> UnPackSizePrefixedMovie(
    const void *buf,
    const flatbuffers::resolver_function_t *res = nullptr) {
  return flatbuffers::unique_ptr<MovieT>(GetSizePrefixedMovie(buf)->UnPack(res));
}

#endif  // FLATBUFFERS_GENERATED_UNIONVECTOR_H_
