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
// struct Vec3, aligned to 8
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq)]
pub struct Vec3(pub [u8; 32]);
impl Default for Vec3 { 
  fn default() -> Self { 
    Self([0; 32])
  }
}
impl core::fmt::Debug for Vec3 {
  fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
    f.debug_struct("Vec3")
      .field("x", &self.x())
      .field("y", &self.y())
      .field("z", &self.z())
      .field("test1", &self.test1())
      .field("test2", &self.test2())
      .field("test3", &self.test3())
      .finish()
  }
}

impl flatbuffers::SimpleToVerifyInSlice for Vec3 {}
impl<'a> flatbuffers::Follow<'a> for Vec3 {
  type Inner = &'a Vec3;
  #[inline]
  unsafe fn follow(buf: &'a [u8], loc: usize) -> Self::Inner {
    <&'a Vec3>::follow(buf, loc)
  }
}
impl<'a> flatbuffers::Follow<'a> for &'a Vec3 {
  type Inner = &'a Vec3;
  #[inline]
  unsafe fn follow(buf: &'a [u8], loc: usize) -> Self::Inner {
    flatbuffers::follow_cast_ref::<Vec3>(buf, loc)
  }
}
impl<'b> flatbuffers::Push for Vec3 {
    type Output = Vec3;
    #[inline]
    unsafe fn push(&self, dst: &mut [u8], _written_len: usize) {
        let src = ::core::slice::from_raw_parts(self as *const Vec3 as *const u8, <Self as flatbuffers::Push>::size());
        dst.copy_from_slice(src);
    }
}

impl<'a> flatbuffers::Verifiable for Vec3 {
  #[inline]
  fn run_verifier(
    v: &mut flatbuffers::Verifier, pos: usize
  ) -> Result<(), flatbuffers::InvalidFlatbuffer> {
    use self::flatbuffers::Verifiable;
    v.in_buffer::<Self>(pos)
  }
}

impl<'a> Vec3 {
  #[allow(clippy::too_many_arguments)]
  pub fn new(
    x: f32,
    y: f32,
    z: f32,
    test1: f64,
    test2: Color,
    test3: &Test,
  ) -> Self {
    let mut s = Self([0; 32]);
    s.set_x(x);
    s.set_y(y);
    s.set_z(z);
    s.set_test1(test1);
    s.set_test2(test2);
    s.set_test3(test3);
    s
  }

  pub const fn get_fully_qualified_name() -> &'static str {
    "MyGame.Example.Vec3"
  }

  pub fn x(&self) -> f32 {
    let mut mem = core::mem::MaybeUninit::<<f32 as EndianScalar>::Scalar>::uninit();
    // Safety:
    // Created from a valid Table for this object
    // Which contains a valid value in this slot
    EndianScalar::from_little_endian(unsafe {
      core::ptr::copy_nonoverlapping(
        self.0[0..].as_ptr(),
        mem.as_mut_ptr() as *mut u8,
        core::mem::size_of::<<f32 as EndianScalar>::Scalar>(),
      );
      mem.assume_init()
    })
  }

  pub fn set_x(&mut self, x: f32) {
    let x_le = x.to_little_endian();
    // Safety:
    // Created from a valid Table for this object
    // Which contains a valid value in this slot
    unsafe {
      core::ptr::copy_nonoverlapping(
        &x_le as *const _ as *const u8,
        self.0[0..].as_mut_ptr(),
        core::mem::size_of::<<f32 as EndianScalar>::Scalar>(),
      );
    }
  }

  pub fn y(&self) -> f32 {
    let mut mem = core::mem::MaybeUninit::<<f32 as EndianScalar>::Scalar>::uninit();
    // Safety:
    // Created from a valid Table for this object
    // Which contains a valid value in this slot
    EndianScalar::from_little_endian(unsafe {
      core::ptr::copy_nonoverlapping(
        self.0[4..].as_ptr(),
        mem.as_mut_ptr() as *mut u8,
        core::mem::size_of::<<f32 as EndianScalar>::Scalar>(),
      );
      mem.assume_init()
    })
  }

  pub fn set_y(&mut self, x: f32) {
    let x_le = x.to_little_endian();
    // Safety:
    // Created from a valid Table for this object
    // Which contains a valid value in this slot
    unsafe {
      core::ptr::copy_nonoverlapping(
        &x_le as *const _ as *const u8,
        self.0[4..].as_mut_ptr(),
        core::mem::size_of::<<f32 as EndianScalar>::Scalar>(),
      );
    }
  }

  pub fn z(&self) -> f32 {
    let mut mem = core::mem::MaybeUninit::<<f32 as EndianScalar>::Scalar>::uninit();
    // Safety:
    // Created from a valid Table for this object
    // Which contains a valid value in this slot
    EndianScalar::from_little_endian(unsafe {
      core::ptr::copy_nonoverlapping(
        self.0[8..].as_ptr(),
        mem.as_mut_ptr() as *mut u8,
        core::mem::size_of::<<f32 as EndianScalar>::Scalar>(),
      );
      mem.assume_init()
    })
  }

  pub fn set_z(&mut self, x: f32) {
    let x_le = x.to_little_endian();
    // Safety:
    // Created from a valid Table for this object
    // Which contains a valid value in this slot
    unsafe {
      core::ptr::copy_nonoverlapping(
        &x_le as *const _ as *const u8,
        self.0[8..].as_mut_ptr(),
        core::mem::size_of::<<f32 as EndianScalar>::Scalar>(),
      );
    }
  }

  pub fn test1(&self) -> f64 {
    let mut mem = core::mem::MaybeUninit::<<f64 as EndianScalar>::Scalar>::uninit();
    // Safety:
    // Created from a valid Table for this object
    // Which contains a valid value in this slot
    EndianScalar::from_little_endian(unsafe {
      core::ptr::copy_nonoverlapping(
        self.0[16..].as_ptr(),
        mem.as_mut_ptr() as *mut u8,
        core::mem::size_of::<<f64 as EndianScalar>::Scalar>(),
      );
      mem.assume_init()
    })
  }

  pub fn set_test1(&mut self, x: f64) {
    let x_le = x.to_little_endian();
    // Safety:
    // Created from a valid Table for this object
    // Which contains a valid value in this slot
    unsafe {
      core::ptr::copy_nonoverlapping(
        &x_le as *const _ as *const u8,
        self.0[16..].as_mut_ptr(),
        core::mem::size_of::<<f64 as EndianScalar>::Scalar>(),
      );
    }
  }

  pub fn test2(&self) -> Color {
    let mut mem = core::mem::MaybeUninit::<<Color as EndianScalar>::Scalar>::uninit();
    // Safety:
    // Created from a valid Table for this object
    // Which contains a valid value in this slot
    EndianScalar::from_little_endian(unsafe {
      core::ptr::copy_nonoverlapping(
        self.0[24..].as_ptr(),
        mem.as_mut_ptr() as *mut u8,
        core::mem::size_of::<<Color as EndianScalar>::Scalar>(),
      );
      mem.assume_init()
    })
  }

  pub fn set_test2(&mut self, x: Color) {
    let x_le = x.to_little_endian();
    // Safety:
    // Created from a valid Table for this object
    // Which contains a valid value in this slot
    unsafe {
      core::ptr::copy_nonoverlapping(
        &x_le as *const _ as *const u8,
        self.0[24..].as_mut_ptr(),
        core::mem::size_of::<<Color as EndianScalar>::Scalar>(),
      );
    }
  }

  pub fn test3(&self) -> &Test {
    // Safety:
    // Created from a valid Table for this object
    // Which contains a valid struct in this slot
    unsafe { &*(self.0[26..].as_ptr() as *const Test) }
  }

  #[allow(clippy::identity_op)]
  pub fn set_test3(&mut self, x: &Test) {
    self.0[26..26 + 4].copy_from_slice(&x.0)
  }

  pub fn unpack(&self) -> Vec3T {
    Vec3T {
      x: self.x(),
      y: self.y(),
      z: self.z(),
      test1: self.test1(),
      test2: self.test2(),
      test3: self.test3().unpack(),
    }
  }
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct Vec3T {
  pub x: f32,
  pub y: f32,
  pub z: f32,
  pub test1: f64,
  pub test2: Color,
  pub test3: TestT,
}
impl Vec3T {
  pub fn pack(&self) -> Vec3 {
    Vec3::new(
      self.x,
      self.y,
      self.z,
      self.test1,
      self.test2,
      &self.test3.pack(),
    )
  }
}

