// automatically generated by the FlatBuffers compiler, do not modify
extern crate flatbuffers;
extern crate core;
extern crate alloc;
use self::alloc::vec::Vec;
use self::alloc::boxed::Box;
use self::alloc::string::{String, ToString as _};
use self::core::mem;
use self::core::cmp::Ordering;
use self::flatbuffers::{EndianScalar, Follow};
use super::*;
pub enum MonsterOffset {}
#[derive(Copy, Clone, PartialEq)]

pub struct Monster<'a> {
  pub _tab: flatbuffers::Table<'a>,
}

impl<'a> flatbuffers::Follow<'a> for Monster<'a> {
  type Inner = Monster<'a>;
  #[inline]
  fn follow(buf: &'a [u8], loc: usize) -> Self::Inner {
    Self { _tab: flatbuffers::Table { buf, loc } }
  }
}

impl<'a> Monster<'a> {
  pub const VT_POS: flatbuffers::VOffsetT = 4;
  pub const VT_MANA: flatbuffers::VOffsetT = 6;
  pub const VT_HP: flatbuffers::VOffsetT = 8;
  pub const VT_NAME: flatbuffers::VOffsetT = 10;
  pub const VT_INVENTORY: flatbuffers::VOffsetT = 14;
  pub const VT_COLOR: flatbuffers::VOffsetT = 16;
  pub const VT_WEAPONS: flatbuffers::VOffsetT = 18;
  pub const VT_EQUIPPED_TYPE: flatbuffers::VOffsetT = 20;
  pub const VT_EQUIPPED: flatbuffers::VOffsetT = 22;
  pub const VT_PATH: flatbuffers::VOffsetT = 24;

  pub const fn get_fully_qualified_name() -> &'static str {
    "MyGame.Sample.Monster"
  }

  #[inline]
  pub fn init_from_table(table: flatbuffers::Table<'a>) -> Self {
    Monster { _tab: table }
  }
  #[allow(unused_mut)]
  pub fn create<'bldr: 'args, 'args: 'mut_bldr, 'mut_bldr>(
    _fbb: &'mut_bldr mut flatbuffers::FlatBufferBuilder<'bldr>,
    args: &'args MonsterArgs<'args>
  ) -> flatbuffers::WIPOffset<Monster<'bldr>> {
    let mut builder = MonsterBuilder::new(_fbb);
    if let Some(x) = args.path { builder.add_path(x); }
    if let Some(x) = args.equipped { builder.add_equipped(x); }
    if let Some(x) = args.weapons { builder.add_weapons(x); }
    if let Some(x) = args.inventory { builder.add_inventory(x); }
    if let Some(x) = args.name { builder.add_name(x); }
    if let Some(x) = args.pos { builder.add_pos(x); }
    builder.add_hp(args.hp);
    builder.add_mana(args.mana);
    builder.add_equipped_type(args.equipped_type);
    builder.add_color(args.color);
    builder.finish()
  }

  pub fn unpack(&self) -> MonsterT {
    let pos = self.pos().map(|x| {
      x.unpack()
    });
    let mana = self.mana();
    let hp = self.hp();
    let name = self.name().map(|x| {
      x.to_string()
    });
    let inventory = self.inventory().map(|x| {
      x.to_vec()
    });
    let color = self.color();
    let weapons = self.weapons().map(|x| {
      x.iter().map(|t| t.unpack()).collect()
    });
    let equipped = match self.equipped_type() {
      Equipment::NONE => EquipmentT::NONE,
      Equipment::Weapon => EquipmentT::Weapon(Box::new(
        self.equipped_as_weapon()
            .expect("Invalid union table, expected `Equipment::Weapon`.")
            .unpack()
      )),
      _ => EquipmentT::NONE,
    };
    let path = self.path().map(|x| {
      x.iter().map(|t| t.unpack()).collect()
    });
    MonsterT {
      pos,
      mana,
      hp,
      name,
      inventory,
      color,
      weapons,
      equipped,
      path,
    }
  }

  #[inline]
  pub fn pos(&self) -> Option<&'a Vec3> {
    self._tab.get::<Vec3>(Monster::VT_POS, None)
  }
  #[inline]
  pub fn mana(&self) -> i16 {
    self._tab.get::<i16>(Monster::VT_MANA, Some(150)).unwrap()
  }
  #[inline]
  pub fn hp(&self) -> i16 {
    self._tab.get::<i16>(Monster::VT_HP, Some(100)).unwrap()
  }
  #[inline]
  pub fn name(&self) -> Option<&'a str> {
    self._tab.get::<flatbuffers::ForwardsUOffset<&str>>(Monster::VT_NAME, None)
  }
  #[inline]
  pub fn inventory(&self) -> Option<&'a [u8]> {
    self._tab.get::<flatbuffers::ForwardsUOffset<flatbuffers::Vector<'a, u8>>>(Monster::VT_INVENTORY, None).map(|v| v.safe_slice())
  }
  #[inline]
  pub fn color(&self) -> Color {
    self._tab.get::<Color>(Monster::VT_COLOR, Some(Color::Blue)).unwrap()
  }
  #[inline]
  pub fn weapons(&self) -> Option<flatbuffers::Vector<'a, flatbuffers::ForwardsUOffset<Weapon<'a>>>> {
    self._tab.get::<flatbuffers::ForwardsUOffset<flatbuffers::Vector<'a, flatbuffers::ForwardsUOffset<Weapon>>>>(Monster::VT_WEAPONS, None)
  }
  #[inline]
  pub fn equipped_type(&self) -> Equipment {
    self._tab.get::<Equipment>(Monster::VT_EQUIPPED_TYPE, Some(Equipment::NONE)).unwrap()
  }
  #[inline]
  pub fn equipped(&self) -> Option<flatbuffers::Table<'a>> {
    self._tab.get::<flatbuffers::ForwardsUOffset<flatbuffers::Table<'a>>>(Monster::VT_EQUIPPED, None)
  }
  #[inline]
  pub fn path(&self) -> Option<&'a [Vec3]> {
    self._tab.get::<flatbuffers::ForwardsUOffset<flatbuffers::Vector<'a, Vec3>>>(Monster::VT_PATH, None).map(|v| v.safe_slice())
  }
  #[inline]
  #[allow(non_snake_case)]
  pub fn equipped_as_weapon(&self) -> Option<Weapon<'a>> {
    if self.equipped_type() == Equipment::Weapon {
      self.equipped().map(Weapon::init_from_table)
    } else {
      None
    }
  }

}

impl flatbuffers::Verifiable for Monster<'_> {
  #[inline]
  fn run_verifier(
    v: &mut flatbuffers::Verifier, pos: usize
  ) -> Result<(), flatbuffers::InvalidFlatbuffer> {
    use self::flatbuffers::Verifiable;
    v.visit_table(pos)?
     .visit_field::<Vec3>("pos", Self::VT_POS, false)?
     .visit_field::<i16>("mana", Self::VT_MANA, false)?
     .visit_field::<i16>("hp", Self::VT_HP, false)?
     .visit_field::<flatbuffers::ForwardsUOffset<&str>>("name", Self::VT_NAME, false)?
     .visit_field::<flatbuffers::ForwardsUOffset<flatbuffers::Vector<'_, u8>>>("inventory", Self::VT_INVENTORY, false)?
     .visit_field::<Color>("color", Self::VT_COLOR, false)?
     .visit_field::<flatbuffers::ForwardsUOffset<flatbuffers::Vector<'_, flatbuffers::ForwardsUOffset<Weapon>>>>("weapons", Self::VT_WEAPONS, false)?
     .visit_union::<Equipment, _>("equipped_type", Self::VT_EQUIPPED_TYPE, "equipped", Self::VT_EQUIPPED, false, |key, v, pos| {
        match key {
          Equipment::Weapon => v.verify_union_variant::<flatbuffers::ForwardsUOffset<Weapon>>("Equipment::Weapon", pos),
          _ => Ok(()),
        }
     })?
     .visit_field::<flatbuffers::ForwardsUOffset<flatbuffers::Vector<'_, Vec3>>>("path", Self::VT_PATH, false)?
     .finish();
    Ok(())
  }
}
pub struct MonsterArgs<'a> {
    pub pos: Option<&'a Vec3>,
    pub mana: i16,
    pub hp: i16,
    pub name: Option<flatbuffers::WIPOffset<&'a str>>,
    pub inventory: Option<flatbuffers::WIPOffset<flatbuffers::Vector<'a, u8>>>,
    pub color: Color,
    pub weapons: Option<flatbuffers::WIPOffset<flatbuffers::Vector<'a, flatbuffers::ForwardsUOffset<Weapon<'a>>>>>,
    pub equipped_type: Equipment,
    pub equipped: Option<flatbuffers::WIPOffset<flatbuffers::UnionWIPOffset>>,
    pub path: Option<flatbuffers::WIPOffset<flatbuffers::Vector<'a, Vec3>>>,
}
impl<'a> Default for MonsterArgs<'a> {
  #[inline]
  fn default() -> Self {
    MonsterArgs {
      pos: None,
      mana: 150,
      hp: 100,
      name: None,
      inventory: None,
      color: Color::Blue,
      weapons: None,
      equipped_type: Equipment::NONE,
      equipped: None,
      path: None,
    }
  }
}
pub struct MonsterBuilder<'a: 'b, 'b> {
  fbb_: &'b mut flatbuffers::FlatBufferBuilder<'a>,
  start_: flatbuffers::WIPOffset<flatbuffers::TableUnfinishedWIPOffset>,
}
impl<'a: 'b, 'b> MonsterBuilder<'a, 'b> {
  #[inline]
  pub fn add_pos(&mut self, pos: &Vec3) {
    self.fbb_.push_slot_always::<&Vec3>(Monster::VT_POS, pos);
  }
  #[inline]
  pub fn add_mana(&mut self, mana: i16) {
    self.fbb_.push_slot::<i16>(Monster::VT_MANA, mana, 150);
  }
  #[inline]
  pub fn add_hp(&mut self, hp: i16) {
    self.fbb_.push_slot::<i16>(Monster::VT_HP, hp, 100);
  }
  #[inline]
  pub fn add_name(&mut self, name: flatbuffers::WIPOffset<&'b  str>) {
    self.fbb_.push_slot_always::<flatbuffers::WIPOffset<_>>(Monster::VT_NAME, name);
  }
  #[inline]
  pub fn add_inventory(&mut self, inventory: flatbuffers::WIPOffset<flatbuffers::Vector<'b , u8>>) {
    self.fbb_.push_slot_always::<flatbuffers::WIPOffset<_>>(Monster::VT_INVENTORY, inventory);
  }
  #[inline]
  pub fn add_color(&mut self, color: Color) {
    self.fbb_.push_slot::<Color>(Monster::VT_COLOR, color, Color::Blue);
  }
  #[inline]
  pub fn add_weapons(&mut self, weapons: flatbuffers::WIPOffset<flatbuffers::Vector<'b , flatbuffers::ForwardsUOffset<Weapon<'b >>>>) {
    self.fbb_.push_slot_always::<flatbuffers::WIPOffset<_>>(Monster::VT_WEAPONS, weapons);
  }
  #[inline]
  pub fn add_equipped_type(&mut self, equipped_type: Equipment) {
    self.fbb_.push_slot::<Equipment>(Monster::VT_EQUIPPED_TYPE, equipped_type, Equipment::NONE);
  }
  #[inline]
  pub fn add_equipped(&mut self, equipped: flatbuffers::WIPOffset<flatbuffers::UnionWIPOffset>) {
    self.fbb_.push_slot_always::<flatbuffers::WIPOffset<_>>(Monster::VT_EQUIPPED, equipped);
  }
  #[inline]
  pub fn add_path(&mut self, path: flatbuffers::WIPOffset<flatbuffers::Vector<'b , Vec3>>) {
    self.fbb_.push_slot_always::<flatbuffers::WIPOffset<_>>(Monster::VT_PATH, path);
  }
  #[inline]
  pub fn new(_fbb: &'b mut flatbuffers::FlatBufferBuilder<'a>) -> MonsterBuilder<'a, 'b> {
    let start = _fbb.start_table();
    MonsterBuilder {
      fbb_: _fbb,
      start_: start,
    }
  }
  #[inline]
  pub fn finish(self) -> flatbuffers::WIPOffset<Monster<'a>> {
    let o = self.fbb_.end_table(self.start_);
    flatbuffers::WIPOffset::new(o.value())
  }
}

impl self::core::fmt::Debug for Monster<'_> {
  fn fmt(&self, f: &mut self::core::fmt::Formatter<'_>) -> self::core::fmt::Result {
    let mut ds = f.debug_struct("Monster");
      ds.field("pos", &self.pos());
      ds.field("mana", &self.mana());
      ds.field("hp", &self.hp());
      ds.field("name", &self.name());
      ds.field("inventory", &self.inventory());
      ds.field("color", &self.color());
      ds.field("weapons", &self.weapons());
      ds.field("equipped_type", &self.equipped_type());
      match self.equipped_type() {
        Equipment::Weapon => {
          if let Some(x) = self.equipped_as_weapon() {
            ds.field("equipped", &x)
          } else {
            ds.field("equipped", &"InvalidFlatbuffer: Union discriminant does not match value.")
          }
        },
        _ => {
          let x: Option<()> = None;
          ds.field("equipped", &x)
        },
      };
      ds.field("path", &self.path());
      ds.finish()
  }
}
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq)]
pub struct MonsterT {
  pub pos: Option<Vec3T>,
  pub mana: i16,
  pub hp: i16,
  pub name: Option<String>,
  pub inventory: Option<Vec<u8>>,
  pub color: Color,
  pub weapons: Option<Vec<WeaponT>>,
  pub equipped: EquipmentT,
  pub path: Option<Vec<Vec3T>>,
}
impl Default for MonsterT {
  fn default() -> Self {
    Self {
      pos: None,
      mana: 150,
      hp: 100,
      name: None,
      inventory: None,
      color: Color::Blue,
      weapons: None,
      equipped: EquipmentT::NONE,
      path: None,
    }
  }
}
impl MonsterT {
  pub fn pack<'b>(
    &self,
    _fbb: &mut flatbuffers::FlatBufferBuilder<'b>
  ) -> flatbuffers::WIPOffset<Monster<'b>> {
    let pos_tmp = self.pos.as_ref().map(|x| x.pack());
    let pos = pos_tmp.as_ref();
    let mana = self.mana;
    let hp = self.hp;
    let name = self.name.as_ref().map(|x|{
      _fbb.create_string(x)
    });
    let inventory = self.inventory.as_ref().map(|x|{
      _fbb.create_vector(x)
    });
    let color = self.color;
    let weapons = self.weapons.as_ref().map(|x|{
      let w: Vec<_> = x.iter().map(|t| t.pack(_fbb)).collect();_fbb.create_vector(&w)
    });
    let equipped_type = self.equipped.equipment_type();
    let equipped = self.equipped.pack(_fbb);
    let path = self.path.as_ref().map(|x|{
      let w: Vec<_> = x.iter().map(|t| t.pack()).collect();_fbb.create_vector(&w)
    });
    Monster::create(_fbb, &MonsterArgs{
      pos,
      mana,
      hp,
      name,
      inventory,
      color,
      weapons,
      equipped_type,
      equipped,
      path,
    })
  }
}
#[inline]
#[deprecated(since="2.0.0", note="Deprecated in favor of `root_as...` methods.")]
pub fn get_root_as_monster<'a>(buf: &'a [u8]) -> Monster<'a> {
  unsafe { flatbuffers::root_unchecked::<Monster<'a>>(buf) }
}

#[inline]
#[deprecated(since="2.0.0", note="Deprecated in favor of `root_as...` methods.")]
pub fn get_size_prefixed_root_as_monster<'a>(buf: &'a [u8]) -> Monster<'a> {
  unsafe { flatbuffers::size_prefixed_root_unchecked::<Monster<'a>>(buf) }
}

#[inline]
/// Verifies that a buffer of bytes contains a `Monster`
/// and returns it.
/// Note that verification is still experimental and may not
/// catch every error, or be maximally performant. For the
/// previous, unchecked, behavior use
/// `root_as_monster_unchecked`.
pub fn root_as_monster(buf: &[u8]) -> Result<Monster, flatbuffers::InvalidFlatbuffer> {
  flatbuffers::root::<Monster>(buf)
}
#[inline]
/// Verifies that a buffer of bytes contains a size prefixed
/// `Monster` and returns it.
/// Note that verification is still experimental and may not
/// catch every error, or be maximally performant. For the
/// previous, unchecked, behavior use
/// `size_prefixed_root_as_monster_unchecked`.
pub fn size_prefixed_root_as_monster(buf: &[u8]) -> Result<Monster, flatbuffers::InvalidFlatbuffer> {
  flatbuffers::size_prefixed_root::<Monster>(buf)
}
#[inline]
/// Verifies, with the given options, that a buffer of bytes
/// contains a `Monster` and returns it.
/// Note that verification is still experimental and may not
/// catch every error, or be maximally performant. For the
/// previous, unchecked, behavior use
/// `root_as_monster_unchecked`.
pub fn root_as_monster_with_opts<'b, 'o>(
  opts: &'o flatbuffers::VerifierOptions,
  buf: &'b [u8],
) -> Result<Monster<'b>, flatbuffers::InvalidFlatbuffer> {
  flatbuffers::root_with_opts::<Monster<'b>>(opts, buf)
}
#[inline]
/// Verifies, with the given verifier options, that a buffer of
/// bytes contains a size prefixed `Monster` and returns
/// it. Note that verification is still experimental and may not
/// catch every error, or be maximally performant. For the
/// previous, unchecked, behavior use
/// `root_as_monster_unchecked`.
pub fn size_prefixed_root_as_monster_with_opts<'b, 'o>(
  opts: &'o flatbuffers::VerifierOptions,
  buf: &'b [u8],
) -> Result<Monster<'b>, flatbuffers::InvalidFlatbuffer> {
  flatbuffers::size_prefixed_root_with_opts::<Monster<'b>>(opts, buf)
}
#[inline]
/// Assumes, without verification, that a buffer of bytes contains a Monster and returns it.
/// # Safety
/// Callers must trust the given bytes do indeed contain a valid `Monster`.
pub unsafe fn root_as_monster_unchecked(buf: &[u8]) -> Monster {
  flatbuffers::root_unchecked::<Monster>(buf)
}
#[inline]
/// Assumes, without verification, that a buffer of bytes contains a size prefixed Monster and returns it.
/// # Safety
/// Callers must trust the given bytes do indeed contain a valid size prefixed `Monster`.
pub unsafe fn size_prefixed_root_as_monster_unchecked(buf: &[u8]) -> Monster {
  flatbuffers::size_prefixed_root_unchecked::<Monster>(buf)
}
#[inline]
pub fn finish_monster_buffer<'a, 'b>(
    fbb: &'b mut flatbuffers::FlatBufferBuilder<'a>,
    root: flatbuffers::WIPOffset<Monster<'a>>) {
  fbb.finish(root, None);
}

#[inline]
pub fn finish_size_prefixed_monster_buffer<'a, 'b>(fbb: &'b mut flatbuffers::FlatBufferBuilder<'a>, root: flatbuffers::WIPOffset<Monster<'a>>) {
  fbb.finish_size_prefixed(root, None);
}
