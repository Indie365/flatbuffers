// automatically generated by the FlatBuffers compiler, do not modify


#ifndef FLATBUFFERS_GENERATED_MONSTER_MYGAME_SAMPLE_H_
#define FLATBUFFERS_GENERATED_MONSTER_MYGAME_SAMPLE_H_

#include "flatbuffers/flatbuffers.h"

namespace MyGame {
namespace Sample {

struct Vec3;

struct Monster;
struct MonsterT;

struct Weapon;
struct WeaponT;

bool operator==(const Vec3 &lhs, const Vec3 &rhs);
bool operator!=(const Vec3 &lhs, const Vec3 &rhs);
bool operator==(const MonsterT &lhs, const MonsterT &rhs);
bool operator!=(const MonsterT &lhs, const MonsterT &rhs);
bool operator==(const WeaponT &lhs, const WeaponT &rhs);
bool operator!=(const WeaponT &lhs, const WeaponT &rhs);

inline const flatbuffers::TypeTable *Vec3TypeTable();

inline const flatbuffers::TypeTable *MonsterTypeTable();

inline const flatbuffers::TypeTable *WeaponTypeTable();

enum Color {
  Color_Red = 0,
  Color_Green = 1,
  Color_Blue = 2,
  Color_MIN = Color_Red,
  Color_MAX = Color_Blue
};

inline const Color (&EnumValuesColor())[3] {
  static const Color values[] = {
    Color_Red,
    Color_Green,
    Color_Blue
  };
  return values;
}

inline const char * const *EnumNamesColor() {
  static const char * const names[4] = {
    "Red",
    "Green",
    "Blue",
    nullptr
  };
  return names;
}

inline const char *EnumNameColor(Color e) {
  if (e < Color_Red || e > Color_Blue) return "";
  const size_t index = static_cast<size_t>(e);
  return EnumNamesColor()[index];
}

enum Equipment {
  Equipment_NONE = 0,
  Equipment_Weapon = 1,
  Equipment_MIN = Equipment_NONE,
  Equipment_MAX = Equipment_Weapon
};

inline const Equipment (&EnumValuesEquipment())[2] {
  static const Equipment values[] = {
    Equipment_NONE,
    Equipment_Weapon
  };
  return values;
}

inline const char * const *EnumNamesEquipment() {
  static const char * const names[3] = {
    "NONE",
    "Weapon",
    nullptr
  };
  return names;
}

inline const char *EnumNameEquipment(Equipment e) {
  if (e < Equipment_NONE || e > Equipment_Weapon) return "";
  const size_t index = static_cast<size_t>(e);
  return EnumNamesEquipment()[index];
}

template<typename T> struct EquipmentTraits {
  static const Equipment enum_value = Equipment_NONE;
};

template<> struct EquipmentTraits<Weapon> {
  static const Equipment enum_value = Equipment_Weapon;
};

struct EquipmentUnion {
  Equipment type;
  void *value;

  EquipmentUnion() : type(Equipment_NONE), value(nullptr) {}
  EquipmentUnion(EquipmentUnion&& u) FLATBUFFERS_NOEXCEPT :
    type(Equipment_NONE), value(nullptr)
    { std::swap(type, u.type); std::swap(value, u.value); }
  EquipmentUnion(const EquipmentUnion &) FLATBUFFERS_NOEXCEPT;
  EquipmentUnion &operator=(const EquipmentUnion &u) FLATBUFFERS_NOEXCEPT
    { EquipmentUnion t(u); std::swap(type, t.type); std::swap(value, t.value); return *this; }
  EquipmentUnion &operator=(EquipmentUnion &&u) FLATBUFFERS_NOEXCEPT
    { std::swap(type, u.type); std::swap(value, u.value); return *this; }
  ~EquipmentUnion() { Reset(); }

  void Reset();

#ifndef FLATBUFFERS_CPP98_STL
  template <typename T>
  void Set(T&& val) {
    using RT = typename std::remove_reference<T>::type;
    Reset();
    type = EquipmentTraits<typename RT::TableType>::enum_value;
    if (type != Equipment_NONE) {
      value = new RT(std::forward<T>(val));
    }
  }
#endif  // FLATBUFFERS_CPP98_STL

  static void *UnPack(const void *obj, Equipment type, const flatbuffers::resolver_function_t *resolver);
  flatbuffers::Offset<void> Pack(flatbuffers::FlatBufferBuilder &_fbb, const flatbuffers::rehasher_function_t *_rehasher = nullptr) const;

  WeaponT *AsWeapon() {
    return type == Equipment_Weapon ?
      reinterpret_cast<WeaponT *>(value) : nullptr;
  }
  const WeaponT *AsWeapon() const {
    return type == Equipment_Weapon ?
      reinterpret_cast<const WeaponT *>(value) : nullptr;
  }
};


inline bool operator==(const EquipmentUnion &lhs, const EquipmentUnion &rhs) {
  if (lhs.type != rhs.type) return false;
  switch (lhs.type) {
    case Equipment_NONE: {
      return true;
    }
    case Equipment_Weapon: {
      return *(reinterpret_cast<const WeaponT *>(lhs.value)) ==
             *(reinterpret_cast<const WeaponT *>(rhs.value));
    }
    default: {
      return false;
    }
  }
}

inline bool operator!=(const EquipmentUnion &lhs, const EquipmentUnion &rhs) {
    return !(lhs == rhs);
}

bool VerifyEquipment(flatbuffers::Verifier &verifier, const void *obj, Equipment type);
bool VerifyEquipmentVector(flatbuffers::Verifier &verifier, const flatbuffers::Vector<flatbuffers::Offset<void>> *values, const flatbuffers::Vector<uint8_t> *types);

FLATBUFFERS_MANUALLY_ALIGNED_STRUCT(4) Vec3 FLATBUFFERS_FINAL_CLASS {
 private:
  float x_;
  float y_;
  float z_;

 public:
  static const flatbuffers::TypeTable *MiniReflectTypeTable() {
    return Vec3TypeTable();
  }
  Vec3() {
    memset(static_cast<void *>(this), 0, sizeof(Vec3));
  }
  Vec3(float _x, float _y, float _z)
      : x_(flatbuffers::EndianScalar(_x)),
        y_(flatbuffers::EndianScalar(_y)),
        z_(flatbuffers::EndianScalar(_z)) {
  }
  float x() const {
    return flatbuffers::EndianScalar(x_);
  }
  void mutate_x(float _x) {
    flatbuffers::WriteScalar(&x_, _x);
  }
  float y() const {
    return flatbuffers::EndianScalar(y_);
  }
  void mutate_y(float _y) {
    flatbuffers::WriteScalar(&y_, _y);
  }
  float z() const {
    return flatbuffers::EndianScalar(z_);
  }
  void mutate_z(float _z) {
    flatbuffers::WriteScalar(&z_, _z);
  }
};
FLATBUFFERS_STRUCT_END(Vec3, 12);

inline bool operator==(const Vec3 &lhs, const Vec3 &rhs) {
  return
      (lhs.x() == rhs.x()) &&
      (lhs.y() == rhs.y()) &&
      (lhs.z() == rhs.z());
}

inline bool operator!=(const Vec3 &lhs, const Vec3 &rhs) {
    return !(lhs == rhs);
}


struct MonsterT : public flatbuffers::NativeTable {
  typedef Monster TableType;
  flatbuffers::unique_ptr<Vec3> pos;
  int16_t mana;
  int16_t hp;
  std::string name;
  std::vector<uint8_t> inventory;
  Color color;
  std::vector<flatbuffers::unique_ptr<WeaponT>> weapons;
  EquipmentUnion equipped;
  std::vector<Vec3> path;
  MonsterT()
      : mana(150),
        hp(100),
        color(Color_Blue) {
  }
};

inline bool operator==(const MonsterT &lhs, const MonsterT &rhs) {
  return
      (lhs.pos == rhs.pos) &&
      (lhs.mana == rhs.mana) &&
      (lhs.hp == rhs.hp) &&
      (lhs.name == rhs.name) &&
      (lhs.inventory == rhs.inventory) &&
      (lhs.color == rhs.color) &&
      (lhs.weapons == rhs.weapons) &&
      (lhs.equipped == rhs.equipped) &&
      (lhs.path == rhs.path);
}

inline bool operator!=(const MonsterT &lhs, const MonsterT &rhs) {
    return !(lhs == rhs);
}


struct Monster FLATBUFFERS_FINAL_CLASS : private flatbuffers::Table {
  typedef MonsterT NativeTableType;
  static const flatbuffers::TypeTable *MiniReflectTypeTable() {
    return MonsterTypeTable();
  }
  enum FlatBuffersVTableOffset FLATBUFFERS_VTABLE_UNDERLYING_TYPE {
    VT_POS = 4,
    VT_MANA = 6,
    VT_HP = 8,
    VT_NAME = 10,
    VT_INVENTORY = 14,
    VT_COLOR = 16,
    VT_WEAPONS = 18,
    VT_EQUIPPED_TYPE = 20,
    VT_EQUIPPED = 22,
    VT_PATH = 24
  };
  const Vec3 *pos() const {
    return GetStruct<const Vec3 *>(VT_POS);
  }
  Vec3 *mutable_pos() {
    return GetStruct<Vec3 *>(VT_POS);
  }
  int16_t mana() const {
    return GetField<int16_t>(VT_MANA, 150);
  }
  bool mutate_mana(int16_t _mana) {
    return SetField<int16_t>(VT_MANA, _mana, 150);
  }
  int16_t hp() const {
    return GetField<int16_t>(VT_HP, 100);
  }
  bool mutate_hp(int16_t _hp) {
    return SetField<int16_t>(VT_HP, _hp, 100);
  }
  const flatbuffers::String *name() const {
    return GetPointer<const flatbuffers::String *>(VT_NAME);
  }
  flatbuffers::String *mutable_name() {
    return GetPointer<flatbuffers::String *>(VT_NAME);
  }
  const flatbuffers::Vector<uint8_t> *inventory() const {
    return GetPointer<const flatbuffers::Vector<uint8_t> *>(VT_INVENTORY);
  }
  flatbuffers::Vector<uint8_t> *mutable_inventory() {
    return GetPointer<flatbuffers::Vector<uint8_t> *>(VT_INVENTORY);
  }
  Color color() const {
    return static_cast<Color>(GetField<int8_t>(VT_COLOR, 2));
  }
  bool mutate_color(Color _color) {
    return SetField<int8_t>(VT_COLOR, static_cast<int8_t>(_color), 2);
  }
  const flatbuffers::Vector<flatbuffers::Offset<Weapon>> *weapons() const {
    return GetPointer<const flatbuffers::Vector<flatbuffers::Offset<Weapon>> *>(VT_WEAPONS);
  }
  flatbuffers::Vector<flatbuffers::Offset<Weapon>> *mutable_weapons() {
    return GetPointer<flatbuffers::Vector<flatbuffers::Offset<Weapon>> *>(VT_WEAPONS);
  }
  Equipment equipped_type() const {
    return static_cast<Equipment>(GetField<uint8_t>(VT_EQUIPPED_TYPE, 0));
  }
  bool mutate_equipped_type(Equipment _equipped_type) {
    return SetField<uint8_t>(VT_EQUIPPED_TYPE, static_cast<uint8_t>(_equipped_type), 0);
  }
  const void *equipped() const {
    return GetPointer<const void *>(VT_EQUIPPED);
  }
  template<typename T> const T *equipped_as() const;
  const Weapon *equipped_as_Weapon() const {
    return equipped_type() == Equipment_Weapon ? static_cast<const Weapon *>(equipped()) : nullptr;
  }
  void *mutable_equipped() {
    return GetPointer<void *>(VT_EQUIPPED);
  }
  const flatbuffers::Vector<const Vec3 *> *path() const {
    return GetPointer<const flatbuffers::Vector<const Vec3 *> *>(VT_PATH);
  }
  flatbuffers::Vector<const Vec3 *> *mutable_path() {
    return GetPointer<flatbuffers::Vector<const Vec3 *> *>(VT_PATH);
  }
  bool Verify(flatbuffers::Verifier &verifier) const {
    return VerifyTableStart(verifier) &&
           VerifyField<Vec3>(verifier, VT_POS) &&
           VerifyField<int16_t>(verifier, VT_MANA) &&
           VerifyField<int16_t>(verifier, VT_HP) &&
           VerifyOffset(verifier, VT_NAME) &&
           verifier.VerifyString(name()) &&
           VerifyOffset(verifier, VT_INVENTORY) &&
           verifier.VerifyVector(inventory()) &&
           VerifyField<int8_t>(verifier, VT_COLOR) &&
           VerifyOffset(verifier, VT_WEAPONS) &&
           verifier.VerifyVector(weapons()) &&
           verifier.VerifyVectorOfTables(weapons()) &&
           VerifyField<uint8_t>(verifier, VT_EQUIPPED_TYPE) &&
           VerifyOffset(verifier, VT_EQUIPPED) &&
           VerifyEquipment(verifier, equipped(), equipped_type()) &&
           VerifyOffset(verifier, VT_PATH) &&
           verifier.VerifyVector(path()) &&
           verifier.EndTable();
  }
  MonsterT *UnPack(const flatbuffers::resolver_function_t *_resolver = nullptr) const;
  void UnPackTo(MonsterT *_o, const flatbuffers::resolver_function_t *_resolver = nullptr) const;
  static flatbuffers::Offset<Monster> Pack(flatbuffers::FlatBufferBuilder &_fbb, const MonsterT* _o, const flatbuffers::rehasher_function_t *_rehasher = nullptr);
};

template<> inline const Weapon *Monster::equipped_as<Weapon>() const {
  return equipped_as_Weapon();
}

struct MonsterBuilder {
  flatbuffers::FlatBufferBuilder &fbb_;
  flatbuffers::uoffset_t start_;
  void add_pos(const Vec3 *pos) {
    fbb_.AddStruct(Monster::VT_POS, pos);
  }
  void add_mana(int16_t mana) {
    fbb_.AddElement<int16_t>(Monster::VT_MANA, mana, 150);
  }
  void add_hp(int16_t hp) {
    fbb_.AddElement<int16_t>(Monster::VT_HP, hp, 100);
  }
  void add_name(flatbuffers::Offset<flatbuffers::String> name) {
    fbb_.AddOffset(Monster::VT_NAME, name);
  }
  void add_inventory(flatbuffers::Offset<flatbuffers::Vector<uint8_t>> inventory) {
    fbb_.AddOffset(Monster::VT_INVENTORY, inventory);
  }
  void add_color(Color color) {
    fbb_.AddElement<int8_t>(Monster::VT_COLOR, static_cast<int8_t>(color), 2);
  }
  void add_weapons(flatbuffers::Offset<flatbuffers::Vector<flatbuffers::Offset<Weapon>>> weapons) {
    fbb_.AddOffset(Monster::VT_WEAPONS, weapons);
  }
  void add_equipped_type(Equipment equipped_type) {
    fbb_.AddElement<uint8_t>(Monster::VT_EQUIPPED_TYPE, static_cast<uint8_t>(equipped_type), 0);
  }
  void add_equipped(flatbuffers::Offset<void> equipped) {
    fbb_.AddOffset(Monster::VT_EQUIPPED, equipped);
  }
  void add_path(flatbuffers::Offset<flatbuffers::Vector<const Vec3 *>> path) {
    fbb_.AddOffset(Monster::VT_PATH, path);
  }
  explicit MonsterBuilder(flatbuffers::FlatBufferBuilder &_fbb)
        : fbb_(_fbb) {
    start_ = fbb_.StartTable();
  }
  MonsterBuilder &operator=(const MonsterBuilder &);
  flatbuffers::Offset<Monster> Finish() {
    const auto end = fbb_.EndTable(start_);
    auto o = flatbuffers::Offset<Monster>(end);
    return o;
  }
};

inline flatbuffers::Offset<Monster> CreateMonster(
    flatbuffers::FlatBufferBuilder &_fbb,
    const Vec3 *pos = 0,
    int16_t mana = 150,
    int16_t hp = 100,
    flatbuffers::Offset<flatbuffers::String> name = 0,
    flatbuffers::Offset<flatbuffers::Vector<uint8_t>> inventory = 0,
    Color color = Color_Blue,
    flatbuffers::Offset<flatbuffers::Vector<flatbuffers::Offset<Weapon>>> weapons = 0,
    Equipment equipped_type = Equipment_NONE,
    flatbuffers::Offset<void> equipped = 0,
    flatbuffers::Offset<flatbuffers::Vector<const Vec3 *>> path = 0) {
  MonsterBuilder builder_(_fbb);
  builder_.add_path(path);
  builder_.add_equipped(equipped);
  builder_.add_weapons(weapons);
  builder_.add_inventory(inventory);
  builder_.add_name(name);
  builder_.add_pos(pos);
  builder_.add_hp(hp);
  builder_.add_mana(mana);
  builder_.add_equipped_type(equipped_type);
  builder_.add_color(color);
  return builder_.Finish();
}

inline flatbuffers::Offset<Monster> CreateMonsterDirect(
    flatbuffers::FlatBufferBuilder &_fbb,
    const Vec3 *pos = 0,
    int16_t mana = 150,
    int16_t hp = 100,
    const char *name = nullptr,
    const std::vector<uint8_t> *inventory = nullptr,
    Color color = Color_Blue,
    const std::vector<flatbuffers::Offset<Weapon>> *weapons = nullptr,
    Equipment equipped_type = Equipment_NONE,
    flatbuffers::Offset<void> equipped = 0,
    const std::vector<Vec3> *path = nullptr) {
  auto name__ = name ? _fbb.CreateString(name) : 0;
  auto inventory__ = inventory ? _fbb.CreateVector<uint8_t>(*inventory) : 0;
  auto weapons__ = weapons ? _fbb.CreateVector<flatbuffers::Offset<Weapon>>(*weapons) : 0;
  auto path__ = path ? _fbb.CreateVectorOfStructs<Vec3>(*path) : 0;
  return MyGame::Sample::CreateMonster(
      _fbb,
      pos,
      mana,
      hp,
      name__,
      inventory__,
      color,
      weapons__,
      equipped_type,
      equipped,
      path__);
}

class GuardedMonster {
  MonsterT native_table_;
 public:
  typedef Monster TableType;
  const MonsterT& NativeTable() const { return native_table_; }
  auto pos() -> decltype(native_table_.pos)&{ return native_table_.pos; }
  auto pos() const -> const decltype(native_table_.pos)&{ return native_table_.pos; }
  auto mana() -> decltype(native_table_.mana)&{ return native_table_.mana; }
  auto mana() const -> const decltype(native_table_.mana)&{ return native_table_.mana; }
  auto hp() -> decltype(native_table_.hp)&{ return native_table_.hp; }
  auto hp() const -> const decltype(native_table_.hp)&{ return native_table_.hp; }
  bool set_name(const std::string& value) {
    native_table_.name = value;
    return true;
  }
  bool set_name(std::string&& value) {
    native_table_.name = std::move(value);
    return true;
  }
  bool swap_name(std::string& value) {
    std::swap(native_table_.name, value);
    return true;
  }
  const std::string& name() const & {
    return native_table_.name;
  }
  void clear_name() {
    native_table_.name.clear();
  }
  bool push_inventory(uint8_t  value) {
    native_table_.inventory.push_back(value);
    return true;
  }
  bool emplace_inventory(uint8_t value) {
    native_table_.inventory.emplace_back(std::move(value));
    return true;
  }
  bool pop_inventory() {
    if (native_table_.inventory.size()) {
      native_table_.inventory.pop_back();
      return true;
    };
    return false;
  }
  bool swap_inventory(std::vector<uint8_t>& value) {
    std::swap(native_table_.inventory, value);
    return true;
  }
  const std::vector<uint8_t>& inventory() const & {
    return native_table_.inventory;
  }
  size_t inventory_size() const {
    return native_table_.inventory.size();
  }
  void clear_inventory() {
    native_table_.inventory.clear();
  }
  auto color() -> decltype(native_table_.color)&{ return native_table_.color; }
  auto color() const -> const decltype(native_table_.color)&{ return native_table_.color; }
  bool emplace_weapons(flatbuffers::unique_ptr<WeaponT> && value) {
    native_table_.weapons.emplace_back(std::move(value));
    return true;
  }
  bool pop_weapons() {
    if (native_table_.weapons.size()) {
      native_table_.weapons.pop_back();
      return true;
    };
    return false;
  }
  bool swap_weapons(std::vector<flatbuffers::unique_ptr<WeaponT>>& value) {
    std::swap(native_table_.weapons, value);
    return true;
  }
  const std::vector<flatbuffers::unique_ptr<WeaponT>>& weapons() const & {
    return native_table_.weapons;
  }
  size_t weapons_size() const {
    return native_table_.weapons.size();
  }
  void clear_weapons() {
    native_table_.weapons.clear();
  }
  auto equipped() -> decltype(native_table_.equipped)&{ return native_table_.equipped; }
  auto equipped() const -> const decltype(native_table_.equipped)&{ return native_table_.equipped; }
  Vec3* add_path() {
    native_table_.path.emplace_back();
    return &native_table_.path.back();
  }
  bool push_path(Vec3 const& value) {
    native_table_.path.push_back(value);
    return true;
  }
  bool emplace_path(Vec3 && value) {
    native_table_.path.emplace_back(std::move(value));
    return true;
  }
  bool pop_path() {
    if (native_table_.path.size()) {
      native_table_.path.pop_back();
      return true;
    };
    return false;
  }
  bool swap_path(std::vector<Vec3>& value) {
    std::swap(native_table_.path, value);
    return true;
  }
  const std::vector<Vec3>& path() const & {
    return native_table_.path;
  }
  size_t path_size() const {
    return native_table_.path.size();
  }
  void clear_path() {
    native_table_.path.clear();
  }
  void clear() {
    native_table_.name.clear();
    native_table_.inventory.clear();
    native_table_.weapons.clear();
    native_table_.path.clear();
  }
};

flatbuffers::Offset<Monster> CreateMonster(flatbuffers::FlatBufferBuilder &_fbb, const MonsterT *_o, const flatbuffers::rehasher_function_t *_rehasher = nullptr);

struct WeaponT : public flatbuffers::NativeTable {
  typedef Weapon TableType;
  std::string name;
  int16_t damage;
  WeaponT()
      : damage(0) {
  }
};

inline bool operator==(const WeaponT &lhs, const WeaponT &rhs) {
  return
      (lhs.name == rhs.name) &&
      (lhs.damage == rhs.damage);
}

inline bool operator!=(const WeaponT &lhs, const WeaponT &rhs) {
    return !(lhs == rhs);
}


struct Weapon FLATBUFFERS_FINAL_CLASS : private flatbuffers::Table {
  typedef WeaponT NativeTableType;
  static const flatbuffers::TypeTable *MiniReflectTypeTable() {
    return WeaponTypeTable();
  }
  enum FlatBuffersVTableOffset FLATBUFFERS_VTABLE_UNDERLYING_TYPE {
    VT_NAME = 4,
    VT_DAMAGE = 6
  };
  const flatbuffers::String *name() const {
    return GetPointer<const flatbuffers::String *>(VT_NAME);
  }
  flatbuffers::String *mutable_name() {
    return GetPointer<flatbuffers::String *>(VT_NAME);
  }
  int16_t damage() const {
    return GetField<int16_t>(VT_DAMAGE, 0);
  }
  bool mutate_damage(int16_t _damage) {
    return SetField<int16_t>(VT_DAMAGE, _damage, 0);
  }
  bool Verify(flatbuffers::Verifier &verifier) const {
    return VerifyTableStart(verifier) &&
           VerifyOffset(verifier, VT_NAME) &&
           verifier.VerifyString(name()) &&
           VerifyField<int16_t>(verifier, VT_DAMAGE) &&
           verifier.EndTable();
  }
  WeaponT *UnPack(const flatbuffers::resolver_function_t *_resolver = nullptr) const;
  void UnPackTo(WeaponT *_o, const flatbuffers::resolver_function_t *_resolver = nullptr) const;
  static flatbuffers::Offset<Weapon> Pack(flatbuffers::FlatBufferBuilder &_fbb, const WeaponT* _o, const flatbuffers::rehasher_function_t *_rehasher = nullptr);
};

struct WeaponBuilder {
  flatbuffers::FlatBufferBuilder &fbb_;
  flatbuffers::uoffset_t start_;
  void add_name(flatbuffers::Offset<flatbuffers::String> name) {
    fbb_.AddOffset(Weapon::VT_NAME, name);
  }
  void add_damage(int16_t damage) {
    fbb_.AddElement<int16_t>(Weapon::VT_DAMAGE, damage, 0);
  }
  explicit WeaponBuilder(flatbuffers::FlatBufferBuilder &_fbb)
        : fbb_(_fbb) {
    start_ = fbb_.StartTable();
  }
  WeaponBuilder &operator=(const WeaponBuilder &);
  flatbuffers::Offset<Weapon> Finish() {
    const auto end = fbb_.EndTable(start_);
    auto o = flatbuffers::Offset<Weapon>(end);
    return o;
  }
};

inline flatbuffers::Offset<Weapon> CreateWeapon(
    flatbuffers::FlatBufferBuilder &_fbb,
    flatbuffers::Offset<flatbuffers::String> name = 0,
    int16_t damage = 0) {
  WeaponBuilder builder_(_fbb);
  builder_.add_name(name);
  builder_.add_damage(damage);
  return builder_.Finish();
}

inline flatbuffers::Offset<Weapon> CreateWeaponDirect(
    flatbuffers::FlatBufferBuilder &_fbb,
    const char *name = nullptr,
    int16_t damage = 0) {
  auto name__ = name ? _fbb.CreateString(name) : 0;
  return MyGame::Sample::CreateWeapon(
      _fbb,
      name__,
      damage);
}

class GuardedWeapon {
  WeaponT native_table_;
 public:
  typedef Weapon TableType;
  const WeaponT& NativeTable() const { return native_table_; }
  bool set_name(const std::string& value) {
    native_table_.name = value;
    return true;
  }
  bool set_name(std::string&& value) {
    native_table_.name = std::move(value);
    return true;
  }
  bool swap_name(std::string& value) {
    std::swap(native_table_.name, value);
    return true;
  }
  const std::string& name() const & {
    return native_table_.name;
  }
  void clear_name() {
    native_table_.name.clear();
  }
  auto damage() -> decltype(native_table_.damage)&{ return native_table_.damage; }
  auto damage() const -> const decltype(native_table_.damage)&{ return native_table_.damage; }
  void clear() {
    native_table_.name.clear();
  }
};

flatbuffers::Offset<Weapon> CreateWeapon(flatbuffers::FlatBufferBuilder &_fbb, const WeaponT *_o, const flatbuffers::rehasher_function_t *_rehasher = nullptr);

inline MonsterT *Monster::UnPack(const flatbuffers::resolver_function_t *_resolver) const {
  auto _o = new MonsterT();
  UnPackTo(_o, _resolver);
  return _o;
}

inline void Monster::UnPackTo(MonsterT *_o, const flatbuffers::resolver_function_t *_resolver) const {
  (void)_o;
  (void)_resolver;
  { auto _e = pos(); if (_e) _o->pos = flatbuffers::unique_ptr<Vec3>(new Vec3(*_e)); };
  { auto _e = mana(); _o->mana = _e; };
  { auto _e = hp(); _o->hp = _e; };
  { auto _e = name(); if (_e) _o->name = _e->str(); };
  { auto _e = inventory(); if (_e) { _o->inventory.resize(_e->size()); for (flatbuffers::uoffset_t _i = 0; _i < _e->size(); _i++) { _o->inventory[_i] = _e->Get(_i); } } };
  { auto _e = color(); _o->color = _e; };
  { auto _e = weapons(); if (_e) { _o->weapons.resize(_e->size()); for (flatbuffers::uoffset_t _i = 0; _i < _e->size(); _i++) { _o->weapons[_i] = flatbuffers::unique_ptr<WeaponT>(_e->Get(_i)->UnPack(_resolver)); } } };
  { auto _e = equipped_type(); _o->equipped.type = _e; };
  { auto _e = equipped(); if (_e) _o->equipped.value = EquipmentUnion::UnPack(_e, equipped_type(), _resolver); };
  { auto _e = path(); if (_e) { _o->path.resize(_e->size()); for (flatbuffers::uoffset_t _i = 0; _i < _e->size(); _i++) { _o->path[_i] = *_e->Get(_i); } } };
}

inline flatbuffers::Offset<Monster> Monster::Pack(flatbuffers::FlatBufferBuilder &_fbb, const MonsterT* _o, const flatbuffers::rehasher_function_t *_rehasher) {
  return CreateMonster(_fbb, _o, _rehasher);
}

inline flatbuffers::Offset<Monster> CreateMonster(flatbuffers::FlatBufferBuilder &_fbb, const MonsterT *_o, const flatbuffers::rehasher_function_t *_rehasher) {
  (void)_rehasher;
  (void)_o;
  struct _VectorArgs { flatbuffers::FlatBufferBuilder *__fbb; const MonsterT* __o; const flatbuffers::rehasher_function_t *__rehasher; } _va = { &_fbb, _o, _rehasher}; (void)_va;
  auto _pos = _o->pos ? _o->pos.get() : 0;
  auto _mana = _o->mana;
  auto _hp = _o->hp;
  auto _name = _o->name.empty() ? 0 : _fbb.CreateString(_o->name);
  auto _inventory = _o->inventory.size() ? _fbb.CreateVector(_o->inventory) : 0;
  auto _color = _o->color;
  auto _weapons = _o->weapons.size() ? _fbb.CreateVector<flatbuffers::Offset<Weapon>> (_o->weapons.size(), [](size_t i, _VectorArgs *__va) { return CreateWeapon(*__va->__fbb, __va->__o->weapons[i].get(), __va->__rehasher); }, &_va ) : 0;
  auto _equipped_type = _o->equipped.type;
  auto _equipped = _o->equipped.Pack(_fbb);
  auto _path = _o->path.size() ? _fbb.CreateVectorOfStructs(_o->path) : 0;
  return MyGame::Sample::CreateMonster(
      _fbb,
      _pos,
      _mana,
      _hp,
      _name,
      _inventory,
      _color,
      _weapons,
      _equipped_type,
      _equipped,
      _path);
}

inline WeaponT *Weapon::UnPack(const flatbuffers::resolver_function_t *_resolver) const {
  auto _o = new WeaponT();
  UnPackTo(_o, _resolver);
  return _o;
}

inline void Weapon::UnPackTo(WeaponT *_o, const flatbuffers::resolver_function_t *_resolver) const {
  (void)_o;
  (void)_resolver;
  { auto _e = name(); if (_e) _o->name = _e->str(); };
  { auto _e = damage(); _o->damage = _e; };
}

inline flatbuffers::Offset<Weapon> Weapon::Pack(flatbuffers::FlatBufferBuilder &_fbb, const WeaponT* _o, const flatbuffers::rehasher_function_t *_rehasher) {
  return CreateWeapon(_fbb, _o, _rehasher);
}

inline flatbuffers::Offset<Weapon> CreateWeapon(flatbuffers::FlatBufferBuilder &_fbb, const WeaponT *_o, const flatbuffers::rehasher_function_t *_rehasher) {
  (void)_rehasher;
  (void)_o;
  struct _VectorArgs { flatbuffers::FlatBufferBuilder *__fbb; const WeaponT* __o; const flatbuffers::rehasher_function_t *__rehasher; } _va = { &_fbb, _o, _rehasher}; (void)_va;
  auto _name = _o->name.empty() ? 0 : _fbb.CreateString(_o->name);
  auto _damage = _o->damage;
  return MyGame::Sample::CreateWeapon(
      _fbb,
      _name,
      _damage);
}

inline bool VerifyEquipment(flatbuffers::Verifier &verifier, const void *obj, Equipment type) {
  switch (type) {
    case Equipment_NONE: {
      return true;
    }
    case Equipment_Weapon: {
      auto ptr = reinterpret_cast<const Weapon *>(obj);
      return verifier.VerifyTable(ptr);
    }
    default: return false;
  }
}

inline bool VerifyEquipmentVector(flatbuffers::Verifier &verifier, const flatbuffers::Vector<flatbuffers::Offset<void>> *values, const flatbuffers::Vector<uint8_t> *types) {
  if (!values || !types) return !values && !types;
  if (values->size() != types->size()) return false;
  for (flatbuffers::uoffset_t i = 0; i < values->size(); ++i) {
    if (!VerifyEquipment(
        verifier,  values->Get(i), types->GetEnum<Equipment>(i))) {
      return false;
    }
  }
  return true;
}

inline void *EquipmentUnion::UnPack(const void *obj, Equipment type, const flatbuffers::resolver_function_t *resolver) {
  switch (type) {
    case Equipment_Weapon: {
      auto ptr = reinterpret_cast<const Weapon *>(obj);
      return ptr->UnPack(resolver);
    }
    default: return nullptr;
  }
}

inline flatbuffers::Offset<void> EquipmentUnion::Pack(flatbuffers::FlatBufferBuilder &_fbb, const flatbuffers::rehasher_function_t *_rehasher) const {
  switch (type) {
    case Equipment_Weapon: {
      auto ptr = reinterpret_cast<const WeaponT *>(value);
      return CreateWeapon(_fbb, ptr, _rehasher).Union();
    }
    default: return 0;
  }
}

inline EquipmentUnion::EquipmentUnion(const EquipmentUnion &u) FLATBUFFERS_NOEXCEPT : type(u.type), value(nullptr) {
  switch (type) {
    case Equipment_Weapon: {
      value = new WeaponT(*reinterpret_cast<WeaponT *>(u.value));
      break;
    }
    default:
      break;
  }
}

inline void EquipmentUnion::Reset() {
  switch (type) {
    case Equipment_Weapon: {
      auto ptr = reinterpret_cast<WeaponT *>(value);
      delete ptr;
      break;
    }
    default: break;
  }
  value = nullptr;
  type = Equipment_NONE;
}

inline const flatbuffers::TypeTable *ColorTypeTable() {
  static const flatbuffers::TypeCode type_codes[] = {
    { flatbuffers::ET_CHAR, 0, 0 },
    { flatbuffers::ET_CHAR, 0, 0 },
    { flatbuffers::ET_CHAR, 0, 0 }
  };
  static const flatbuffers::TypeFunction type_refs[] = {
    ColorTypeTable
  };
  static const char * const names[] = {
    "Red",
    "Green",
    "Blue"
  };
  static const flatbuffers::TypeTable tt = {
    flatbuffers::ST_ENUM, 3, type_codes, type_refs, nullptr, names
  };
  return &tt;
}

inline const flatbuffers::TypeTable *EquipmentTypeTable() {
  static const flatbuffers::TypeCode type_codes[] = {
    { flatbuffers::ET_SEQUENCE, 0, -1 },
    { flatbuffers::ET_SEQUENCE, 0, 0 }
  };
  static const flatbuffers::TypeFunction type_refs[] = {
    WeaponTypeTable
  };
  static const char * const names[] = {
    "NONE",
    "Weapon"
  };
  static const flatbuffers::TypeTable tt = {
    flatbuffers::ST_UNION, 2, type_codes, type_refs, nullptr, names
  };
  return &tt;
}

inline const flatbuffers::TypeTable *Vec3TypeTable() {
  static const flatbuffers::TypeCode type_codes[] = {
    { flatbuffers::ET_FLOAT, 0, -1 },
    { flatbuffers::ET_FLOAT, 0, -1 },
    { flatbuffers::ET_FLOAT, 0, -1 }
  };
  static const int64_t values[] = { 0, 4, 8, 12 };
  static const char * const names[] = {
    "x",
    "y",
    "z"
  };
  static const flatbuffers::TypeTable tt = {
    flatbuffers::ST_STRUCT, 3, type_codes, nullptr, values, names
  };
  return &tt;
}

inline const flatbuffers::TypeTable *MonsterTypeTable() {
  static const flatbuffers::TypeCode type_codes[] = {
    { flatbuffers::ET_SEQUENCE, 0, 0 },
    { flatbuffers::ET_SHORT, 0, -1 },
    { flatbuffers::ET_SHORT, 0, -1 },
    { flatbuffers::ET_STRING, 0, -1 },
    { flatbuffers::ET_BOOL, 0, -1 },
    { flatbuffers::ET_UCHAR, 1, -1 },
    { flatbuffers::ET_CHAR, 0, 1 },
    { flatbuffers::ET_SEQUENCE, 1, 2 },
    { flatbuffers::ET_UTYPE, 0, 3 },
    { flatbuffers::ET_SEQUENCE, 0, 3 },
    { flatbuffers::ET_SEQUENCE, 1, 0 }
  };
  static const flatbuffers::TypeFunction type_refs[] = {
    Vec3TypeTable,
    ColorTypeTable,
    WeaponTypeTable,
    EquipmentTypeTable
  };
  static const char * const names[] = {
    "pos",
    "mana",
    "hp",
    "name",
    "friendly",
    "inventory",
    "color",
    "weapons",
    "equipped_type",
    "equipped",
    "path"
  };
  static const flatbuffers::TypeTable tt = {
    flatbuffers::ST_TABLE, 11, type_codes, type_refs, nullptr, names
  };
  return &tt;
}

inline const flatbuffers::TypeTable *WeaponTypeTable() {
  static const flatbuffers::TypeCode type_codes[] = {
    { flatbuffers::ET_STRING, 0, -1 },
    { flatbuffers::ET_SHORT, 0, -1 }
  };
  static const char * const names[] = {
    "name",
    "damage"
  };
  static const flatbuffers::TypeTable tt = {
    flatbuffers::ST_TABLE, 2, type_codes, nullptr, nullptr, names
  };
  return &tt;
}

inline const MyGame::Sample::Monster *GetMonster(const void *buf) {
  return flatbuffers::GetRoot<MyGame::Sample::Monster>(buf);
}

inline const MyGame::Sample::Monster *GetSizePrefixedMonster(const void *buf) {
  return flatbuffers::GetSizePrefixedRoot<MyGame::Sample::Monster>(buf);
}

inline Monster *GetMutableMonster(void *buf) {
  return flatbuffers::GetMutableRoot<Monster>(buf);
}

inline bool VerifyMonsterBuffer(
    flatbuffers::Verifier &verifier) {
  return verifier.VerifyBuffer<MyGame::Sample::Monster>(nullptr);
}

inline bool VerifySizePrefixedMonsterBuffer(
    flatbuffers::Verifier &verifier) {
  return verifier.VerifySizePrefixedBuffer<MyGame::Sample::Monster>(nullptr);
}

inline void FinishMonsterBuffer(
    flatbuffers::FlatBufferBuilder &fbb,
    flatbuffers::Offset<MyGame::Sample::Monster> root) {
  fbb.Finish(root);
}

inline void FinishSizePrefixedMonsterBuffer(
    flatbuffers::FlatBufferBuilder &fbb,
    flatbuffers::Offset<MyGame::Sample::Monster> root) {
  fbb.FinishSizePrefixed(root);
}

inline flatbuffers::unique_ptr<MonsterT> UnPackMonster(
    const void *buf,
    const flatbuffers::resolver_function_t *res = nullptr) {
  return flatbuffers::unique_ptr<MonsterT>(GetMonster(buf)->UnPack(res));
}

}  // namespace Sample
}  // namespace MyGame

#endif  // FLATBUFFERS_GENERATED_MONSTER_MYGAME_SAMPLE_H_
