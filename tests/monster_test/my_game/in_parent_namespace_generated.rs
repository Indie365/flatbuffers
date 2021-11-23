// automatically generated by the FlatBuffers compiler, do not modify
extern crate flatbuffers;
use std::mem;
use std::cmp::Ordering;
use self::flatbuffers::{EndianScalar, Follow};
use super::*;
pub enum InParentNamespaceOffset {}
#[derive(Copy, Clone, PartialEq)]

pub struct InParentNamespace<'a> {
  pub _tab: flatbuffers::Table<'a>,
}

impl<'a> flatbuffers::Follow<'a> for InParentNamespace<'a> {
  type Inner = InParentNamespace<'a>;
  #[inline]
  unsafe fn follow(buf: &'a [u8], loc: usize) -> Self::Inner {
    Self { _tab: flatbuffers::Table { buf, loc } }
  }
}

impl<'a> InParentNamespace<'a> {

  pub const fn get_fully_qualified_name() -> &'static str {
    "MyGame.InParentNamespace"
  }

  #[inline]
  pub fn init_from_table(table: flatbuffers::Table<'a>) -> Self {
    InParentNamespace { _tab: table }
  }
  #[allow(unused_mut)]
  pub fn create<'bldr: 'args, 'args: 'mut_bldr, 'mut_bldr>(
    _fbb: &'mut_bldr mut flatbuffers::FlatBufferBuilder<'bldr>,
    _args: &'args InParentNamespaceArgs
  ) -> flatbuffers::WIPOffset<InParentNamespace<'bldr>> {
    let mut builder = InParentNamespaceBuilder::new(_fbb);
    builder.finish()
  }

  pub fn unpack(&self) -> InParentNamespaceT {
    InParentNamespaceT {
    }
  }
}

impl flatbuffers::Verifiable for InParentNamespace<'_> {
  #[inline]
  fn run_verifier(
    v: &mut flatbuffers::Verifier, pos: usize
  ) -> Result<(), flatbuffers::InvalidFlatbuffer> {
    use self::flatbuffers::Verifiable;
    v.visit_table(pos)?
     .finish();
    Ok(())
  }
}
pub struct InParentNamespaceArgs {
}
impl<'a> Default for InParentNamespaceArgs {
  #[inline]
  fn default() -> Self {
    InParentNamespaceArgs {
    }
  }
}
pub struct InParentNamespaceBuilder<'a: 'b, 'b> {
  fbb_: &'b mut flatbuffers::FlatBufferBuilder<'a>,
  start_: flatbuffers::WIPOffset<flatbuffers::TableUnfinishedWIPOffset>,
}
impl<'a: 'b, 'b> InParentNamespaceBuilder<'a, 'b> {
  #[inline]
  pub fn new(_fbb: &'b mut flatbuffers::FlatBufferBuilder<'a>) -> InParentNamespaceBuilder<'a, 'b> {
    let start = _fbb.start_table();
    InParentNamespaceBuilder {
      fbb_: _fbb,
      start_: start,
    }
  }
  #[inline]
  pub fn finish(self) -> flatbuffers::WIPOffset<InParentNamespace<'a>> {
    let o = self.fbb_.end_table(self.start_);
    flatbuffers::WIPOffset::new(o.value())
  }
}

impl std::fmt::Debug for InParentNamespace<'_> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let mut ds = f.debug_struct("InParentNamespace");
      ds.finish()
  }
}
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq)]
pub struct InParentNamespaceT {
}
impl Default for InParentNamespaceT {
  fn default() -> Self {
    Self {
    }
  }
}
impl InParentNamespaceT {
  pub fn pack<'b>(
    &self,
    _fbb: &mut flatbuffers::FlatBufferBuilder<'b>
  ) -> flatbuffers::WIPOffset<InParentNamespace<'b>> {
    InParentNamespace::create(_fbb, &InParentNamespaceArgs{
    })
  }
}
