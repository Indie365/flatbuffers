/*
 * Copyright 2021 Google Inc. All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use crate::follow::Follow;
use crate::{
    vector::{SafeSliceAccess, VectorIter},
    EndianScalar,
};
use std::fmt::{Debug, Formatter, Result};
use std::marker::PhantomData;
use std::mem::size_of;
use std::slice::from_raw_parts;

#[derive(Copy, Clone)]
pub struct Array<'a, T: 'a, const N: usize>(&'a [u8], PhantomData<T>);

impl<'a, T: 'a, const N: usize> Debug for Array<'a, T, N>
where
    T: 'a + Follow<'a>,
    <T as Follow<'a>>::Inner: Debug,
{
    fn fmt(&self, f: &mut Formatter) -> Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<'a, T: 'a, const N: usize> Array<'a, T, N> {
    #[inline(always)]
    pub fn new(buf: &'a [u8]) -> Self {
        debug_assert!(size_of::<T>() * N == buf.len());

        Array {
            0: buf,
            1: PhantomData,
        }
    }

    #[inline(always)]
    pub fn len(&self) -> usize {
        N
    }
}

impl<'a, T: Follow<'a> + 'a, const N: usize> Array<'a, T, N> {
    #[inline(always)]
    pub fn get(&self, idx: usize) -> T::Inner {
        debug_assert!(idx < N);
        let sz = size_of::<T>();
        T::follow(self.0, sz * idx)
    }

    #[inline(always)]
    pub fn iter(&self) -> VectorIter<'a, T> {
        VectorIter::from_slice(self.0, self.len())
    }
}

impl<'a, T: Follow<'a> + Debug, const N: usize> Into<[T::Inner; N]> for Array<'a, T, N> {
    fn into(self) -> [T::Inner; N] {
        let mut mem = core::mem::MaybeUninit::<[T::Inner; N]>::uninit();
        let mut mem_ptr = mem.as_mut_ptr() as *mut T::Inner;
        unsafe {
            for item in self.iter() {
                mem_ptr.write(item);
                mem_ptr = mem_ptr.add(1);
            }
            mem.assume_init()
        }
    }
}

impl<'a, T: SafeSliceAccess + 'a, const N: usize> Array<'a, T, N> {
    pub fn safe_slice(self) -> &'a [T] {
        let sz = size_of::<T>();
        debug_assert!(sz > 0);
        let ptr = self.0.as_ptr() as *const T;
        unsafe { from_raw_parts(ptr, N) }
    }
}

/// Implement Follow for all possible Arrays that have Follow-able elements.
impl<'a, T: Follow<'a> + 'a, const N: usize> Follow<'a> for Array<'a, T, N> {
    type Inner = Array<'a, T, N>;
    fn follow(buf: &'a [u8], loc: usize) -> Self::Inner {
        Array::new(&buf[loc..loc + N * size_of::<T>()])
    }
}

pub fn emplace_scalar_array<T: EndianScalar, const N: usize>(
    buf: &mut [u8],
    loc: usize,
    src: &[T; N],
) {
    let mut buf_ptr = buf[loc..].as_mut_ptr() as *mut T;
    for item in src.iter() {
        let item_le = item.to_little_endian();
        unsafe {
            buf_ptr.write(item_le);
            buf_ptr = buf_ptr.add(1);
        }
    }
}

impl<'a, T: Follow<'a> + 'a, const N: usize> IntoIterator for Array<'a, T, N> {
    type Item = T::Inner;
    type IntoIter = VectorIter<'a, T>;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
