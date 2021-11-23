// automatically generated by the FlatBuffers compiler, do not modify
extern crate flatbuffers;
use std::mem;
use std::cmp::Ordering;
use self::flatbuffers::{EndianScalar, Follow};
use super::*;
#[deprecated(since = "2.0.0", note = "Use associated constants instead. This will no longer be generated in 2021.")]
pub const ENUM_MIN_PUBLIC: i32 = 0;
#[deprecated(since = "2.0.0", note = "Use associated constants instead. This will no longer be generated in 2021.")]
pub const ENUM_MAX_PUBLIC: i32 = 0;
#[deprecated(since = "2.0.0", note = "Use associated constants instead. This will no longer be generated in 2021.")]
#[allow(non_camel_case_types)]
pub const ENUM_VALUES_PUBLIC: [public; 1] = [
  public::NONE,
];

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
#[repr(transparent)]
pub struct public(pub i32);
#[allow(non_upper_case_globals)]
impl public {
  pub const NONE: Self = Self(0);

  pub const ENUM_MIN: i32 = 0;
  pub const ENUM_MAX: i32 = 0;
  pub const ENUM_VALUES: &'static [Self] = &[
    Self::NONE,
  ];
  /// Returns the variant's name or "" if unknown.
  pub fn variant_name(self) -> Option<&'static str> {
    match self {
      Self::NONE => Some("NONE"),
      _ => None,
    }
  }
}
impl std::fmt::Debug for public {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    if let Some(name) = self.variant_name() {
      f.write_str(name)
    } else {
      f.write_fmt(format_args!("<UNKNOWN {:?}>", self.0))
    }
  }
}
impl<'a> flatbuffers::Follow<'a> for public {
  type Inner = Self;
  #[inline]
  unsafe fn follow(buf: &'a [u8], loc: usize) -> Self::Inner {
    let b = unsafe {
      flatbuffers::read_scalar_at::<i32>(buf, loc)
    };
    Self(b)
  }
}

impl flatbuffers::Push for public {
    type Output = public;
    #[inline]
    fn push(&self, dst: &mut [u8], _rest: &[u8]) {
        unsafe { flatbuffers::emplace_scalar::<i32>(dst, self.0); }
    }
}

impl flatbuffers::EndianScalar for public {
  #[inline]
  fn to_little_endian(self) -> Self {
    let b = i32::to_le(self.0);
    Self(b)
  }
  #[inline]
  #[allow(clippy::wrong_self_convention)]
  fn from_little_endian(self) -> Self {
    let b = i32::from_le(self.0);
    Self(b)
  }
}

impl<'a> flatbuffers::Verifiable for public {
  #[inline]
  fn run_verifier(
    v: &mut flatbuffers::Verifier, pos: usize
  ) -> Result<(), flatbuffers::InvalidFlatbuffer> {
    use self::flatbuffers::Verifiable;
    i32::run_verifier(v, pos)
  }
}

impl flatbuffers::SimpleToVerifyInSlice for public {}
