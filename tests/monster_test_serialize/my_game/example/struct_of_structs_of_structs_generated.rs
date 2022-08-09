// @generated
// automatically generated by the FlatBuffers compiler, do not modify
extern crate alloc;
extern crate flatbuffers;
use alloc::boxed::Box;
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use core::mem;
use core::cmp::Ordering;
extern crate serde;
use self::serde::ser::{Serialize, Serializer, SerializeStruct};
use self::flatbuffers::{EndianScalar, Follow};
use super::*;
// struct StructOfStructsOfStructs, aligned to 4
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq)]
pub struct StructOfStructsOfStructs(pub [u8; 20]);
impl Default for StructOfStructsOfStructs { 
  fn default() -> Self { 
    Self([0; 20])
  }
}
impl core::fmt::Debug for StructOfStructsOfStructs {
  fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
    f.debug_struct("StructOfStructsOfStructs")
      .field("a", &self.a())
      .finish()
  }
}

impl flatbuffers::SimpleToVerifyInSlice for StructOfStructsOfStructs {}
impl flatbuffers::SafeSliceAccess for StructOfStructsOfStructs {}
impl<'a> flatbuffers::Follow<'a> for StructOfStructsOfStructs {
  type Inner = &'a StructOfStructsOfStructs;
  #[inline]
  fn follow(buf: &'a [u8], loc: usize) -> Self::Inner {
    <&'a StructOfStructsOfStructs>::follow(buf, loc)
  }
}
impl<'a> flatbuffers::Follow<'a> for &'a StructOfStructsOfStructs {
  type Inner = &'a StructOfStructsOfStructs;
  #[inline]
  fn follow(buf: &'a [u8], loc: usize) -> Self::Inner {
    flatbuffers::follow_cast_ref::<StructOfStructsOfStructs>(buf, loc)
  }
}
impl<'b> flatbuffers::Push for StructOfStructsOfStructs {
    type Output = StructOfStructsOfStructs;
    #[inline]
    fn push(&self, dst: &mut [u8], _rest: &[u8]) {
        let src = unsafe {
            ::core::slice::from_raw_parts(self as *const StructOfStructsOfStructs as *const u8, Self::size())
        };
        dst.copy_from_slice(src);
    }
}
impl<'b> flatbuffers::Push for &'b StructOfStructsOfStructs {
    type Output = StructOfStructsOfStructs;

    #[inline]
    fn push(&self, dst: &mut [u8], _rest: &[u8]) {
        let src = unsafe {
            ::core::slice::from_raw_parts(*self as *const StructOfStructsOfStructs as *const u8, Self::size())
        };
        dst.copy_from_slice(src);
    }
}

impl<'a> flatbuffers::Verifiable for StructOfStructsOfStructs {
  #[inline]
  fn run_verifier(
    v: &mut flatbuffers::Verifier, pos: usize
  ) -> Result<(), flatbuffers::InvalidFlatbuffer> {
    use self::flatbuffers::Verifiable;
    v.in_buffer::<Self>(pos)
  }
}

impl Serialize for StructOfStructsOfStructs {
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: Serializer,
  {
    let mut s = serializer.serialize_struct("StructOfStructsOfStructs", 1)?;
      s.serialize_field("a", &self.a())?;
    s.end()
  }
}

impl<'a> StructOfStructsOfStructs {
  #[allow(clippy::too_many_arguments)]
  pub fn new(
    a: &StructOfStructs,
  ) -> Self {
    let mut s = Self([0; 20]);
    s.set_a(a);
    s
  }

  pub const fn get_fully_qualified_name() -> &'static str {
    "MyGame.Example.StructOfStructsOfStructs"
  }

  pub fn a(&self) -> &StructOfStructs {
    unsafe { &*(self.0[0..].as_ptr() as *const StructOfStructs) }
  }

  #[allow(clippy::identity_op)]
  pub fn set_a(&mut self, x: &StructOfStructs) {
    self.0[0..0 + 20].copy_from_slice(&x.0)
  }

  pub fn unpack(&self) -> StructOfStructsOfStructsT {
    StructOfStructsOfStructsT {
      a: self.a().unpack(),
    }
  }
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct StructOfStructsOfStructsT {
  pub a: StructOfStructsT,
}
impl StructOfStructsOfStructsT {
  pub fn pack(&self) -> StructOfStructsOfStructs {
    StructOfStructsOfStructs::new(
      &self.a.pack(),
    )
  }
}

