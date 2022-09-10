// automatically generated by the FlatBuffers compiler, do not modify
// @generated
extern crate alloc;
extern crate flatbuffers;
use alloc::boxed::Box;
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use core::mem;
use core::cmp::Ordering;
use self::flatbuffers::{EndianScalar, Follow};
use super::*;
pub(crate) enum AnnotationsOffset {}
#[derive(Copy, Clone, PartialEq)]

pub(crate) struct Annotations<'a> {
  pub _tab: flatbuffers::Table<'a>,
}

impl<'a> flatbuffers::Follow<'a> for Annotations<'a> {
  type Inner = Annotations<'a>;
  #[inline]
  unsafe fn follow(buf: &'a [u8], loc: usize) -> Self::Inner {
    Self { _tab: flatbuffers::Table::new(buf, loc) }
  }
}

impl<'a> Annotations<'a> {
  pub const VT_VALUE: flatbuffers::VOffsetT = 4;

  pub const fn get_fully_qualified_name() -> &'static str {
    "Annotations"
  }

  #[inline]
  pub unsafe fn init_from_table(table: flatbuffers::Table<'a>) -> Self {
    Annotations { _tab: table }
  }
  #[allow(unused_mut)]
  pub fn create<'bldr: 'args, 'args: 'mut_bldr, 'mut_bldr>(
    _fbb: &'mut_bldr mut flatbuffers::FlatBufferBuilder<'bldr>,
    args: &'args AnnotationsArgs
  ) -> flatbuffers::WIPOffset<Annotations<'bldr>> {
    let mut builder = AnnotationsBuilder::new(_fbb);
    builder.add_value(args.value);
    builder.finish()
  }

  pub fn unpack(&self) -> AnnotationsT {
    let value = self.value();
    AnnotationsT {
      value,
    }
  }

  #[inline]
  pub fn value(&self) -> i32 {
    unsafe { self._tab.get::<i32>(Annotations::VT_VALUE, Some(0)).unwrap()}
  }
}

impl flatbuffers::Verifiable for Annotations<'_> {
  #[inline]
  fn run_verifier(
    v: &mut flatbuffers::Verifier, pos: usize
  ) -> Result<(), flatbuffers::InvalidFlatbuffer> {
    use self::flatbuffers::Verifiable;
    v.visit_table(pos)?
     .visit_field::<i32>("value", Self::VT_VALUE, false)?
     .finish();
    Ok(())
  }
}
pub(crate) struct AnnotationsArgs {
    pub value: i32,
}
impl<'a> Default for AnnotationsArgs {
  #[inline]
  fn default() -> Self {
    AnnotationsArgs {
      value: 0,
    }
  }
}

pub(crate) struct AnnotationsBuilder<'a: 'b, 'b> {
  fbb_: &'b mut flatbuffers::FlatBufferBuilder<'a>,
  start_: flatbuffers::WIPOffset<flatbuffers::TableUnfinishedWIPOffset>,
}
impl<'a: 'b, 'b> AnnotationsBuilder<'a, 'b> {
  #[inline]
  pub fn add_value(&mut self, value: i32) {
    self.fbb_.push_slot::<i32>(Annotations::VT_VALUE, value, 0);
  }
  #[inline]
  pub fn new(_fbb: &'b mut flatbuffers::FlatBufferBuilder<'a>) -> AnnotationsBuilder<'a, 'b> {
    let start = _fbb.start_table();
    AnnotationsBuilder {
      fbb_: _fbb,
      start_: start,
    }
  }
  #[inline]
  pub fn finish(self) -> flatbuffers::WIPOffset<Annotations<'a>> {
    let o = self.fbb_.end_table(self.start_);
    flatbuffers::WIPOffset::new(o.value())
  }
}

impl core::fmt::Debug for Annotations<'_> {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    let mut ds = f.debug_struct("Annotations");
      ds.field("value", &self.value());
      ds.finish()
  }
}
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct AnnotationsT {
  pub value: i32,
}
impl Default for AnnotationsT {
  fn default() -> Self {
    Self {
      value: 0,
    }
  }
}
impl AnnotationsT {
  pub fn pack<'b>(
    &self,
    _fbb: &mut flatbuffers::FlatBufferBuilder<'b>
  ) -> flatbuffers::WIPOffset<Annotations<'b>> {
    let value = self.value;
    Annotations::create(_fbb, &AnnotationsArgs{
      value,
    })
  }
}
