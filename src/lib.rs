//!
//! [![Version](https://img.shields.io/crates/v/teeint)](https://crates.io/crates/teeint)
//! [![Downloads](https://img.shields.io/crates/d/teeint)](https://crates.io/crates/teeint)
//! [![License](https://img.shields.io/crates/l/teeint)](https://crates.io/crates/teeint)
//! ![Rust](https://github.com/edg-l/teeint/workflows/Rust/badge.svg)
//! [![Docs](https://docs.rs/teeint/badge.svg)](https://docs.rs/teeint)
//!
//! A teeworlds variable integer packer/unpacker.
//!
//!
//! ## Packing
//!
//! ```
//! use std::io::Cursor;
//!
//! let mut buff = Cursor::new([0; 2]);
//!
//! teeint::pack(&mut buff, 64).unwrap();
//!
//! let buff = buff.into_inner();
//! assert_eq!(buff[0], 0b1000_0000);
//! assert_eq!(buff[1], 0b0000_0001);
//! ```
//!
//! Or using the trait [`PackTwInt`]:
//! ```
//! use std::io::Cursor;
//! use teeint::PackTwInt;
//!
//! let mut buff = Cursor::new([0; 2]);
//!
//! 64.pack(&mut buff).unwrap();
//!
//! let buff = buff.into_inner();
//! assert_eq!(buff[0], 0b1000_0000);
//! assert_eq!(buff[1], 0b0000_0001);
//! ```
//!
//! Or
//! ```
//! use teeint::PackTwInt;
//!
//! let mut buff = [0; 2];
//! 64.pack(&mut buff.as_mut_slice()).unwrap();
//! assert_eq!(buff[0], 0b1000_0000);
//! assert_eq!(buff[1], 0b0000_0001);
//! ```
//!
//! ## Unpacking
//! ```
//! use std::io::Cursor;
//!
//! let mut buff = Cursor::new([0b1000_0000, 0b0000_0001]);
//! let data = teeint::unpack(&mut buff).unwrap();
//! assert_eq!(data, 64);
//! ```
//!
//! Or using the trait [`UnPackTwInt`]:
//! ```
//! use teeint::UnPackTwInt;
//!
//! let buff = [0b1000_0000, 0b0000_0001];
//! let result = buff.as_slice().unpack().unwrap();
//! assert_eq!(result, 64);
//! ```

#![forbid(unsafe_code)]
#![deny(missing_docs)]
#![deny(warnings)]
#![deny(clippy::nursery)]
#![deny(clippy::pedantic)]
#![deny(clippy::all)]

use std::io::{Read, Result, Write};

/// Max bytes packed in a variable int.
pub const MAX_BYTES_PACKED: usize = 5;

/// Pack a i32 into a teeworlds variable integer.
///
/// # Errors
/// Returns `Err` if there is an error writing to `dst`.
#[inline]
pub fn pack<T: Write + ?Sized>(dst: &mut T, mut value: i32) -> Result<()> {
    let mut current_byte: u8 = 0;

    /*
     *  First byte: BIT_EXTEND BIT_SIGN BITS[6]
     *  Next byte:  BIT_EXTEND BITS[7]
     *  Last byte:  BIT_PADDING[4] BITS[4]
     */

    // If value is negative, set the sign bit and flip all the bits.
    if value < 0 {
        current_byte = 0b0100_0000;
        value = !value;
    }

    // First byte: Pack the remaining 6 bits
    current_byte |= u8::try_from(value & 0b0011_1111).expect("should always be inside the range");
    value >>= 6;

    while value != 0 {
        // We have more data, set BIT_EXTEND
        current_byte |= 0b1000_0000;
        dst.write_all(std::slice::from_ref(&current_byte))?;
        // Write the BITS[7]
        current_byte =
            u8::try_from(value & 0b0111_1111).expect("should always be inside the range");
        // Discard them.
        value >>= 7;
    }

    dst.write_all(std::slice::from_ref(&current_byte))?;

    Ok(())
}

/// Unpack a teeworlds variable int from the provided reader.
///
/// # Errors
/// Returns `Err` if there is an error reading from `src`
#[inline]
pub fn unpack<T: Read + ?Sized>(src: &mut T) -> Result<i32> {
    const MASKS: [i32; 4] = [0x7F, 0x7F, 0x7F, 0x0F];
    const SHIFTS: [i32; 4] = [6, 6 + 7, 6 + 7 + 7, 6 + 7 + 7 + 7];

    // Adapted from https://github.com/ddnet/ddnet/blob/79df5893ff26fa75d67e46f99e58f75b739ac362/src/engine/shared/compression.cpp#L10
    let mut result: i32;
    let mut current_byte: u8 = 0;

    src.read_exact(std::slice::from_mut(&mut current_byte))?;
    let sign = (current_byte >> 6) & 1;
    result = i32::from(current_byte & 0x3F);

    for (mask, shift) in MASKS.into_iter().zip(SHIFTS.into_iter()) {
        if (current_byte & 0x80) == 0 {
            break;
        }

        src.read_exact(std::slice::from_mut(&mut current_byte))?;
        result |= (i32::from(current_byte) & mask) << shift;
    }

    result ^= -i32::from(sign);

    Ok(result)
}

/// Trait implemented by values that can be packed to a teeworlds variable int.
///
/// Note that teeworlds only packs i32 values.
///
/// This trait is more of a convenience to allow writing `0i32.pack(&mut buff)`
pub trait PackTwInt {
    /// Pack this value into a teeworlds variable int.
    ///
    /// # Errors
    /// Returns `Err` if there is an error writing to `dst`.
    fn pack<T: Write + ?Sized>(self, dst: &mut T) -> Result<()>;
}

impl PackTwInt for i32 {
    #[inline]
    fn pack<T: Write + ?Sized>(self, dst: &mut T) -> Result<()> {
        pack(dst, self)
    }
}

/// Trait implemented by buffers holding a teeworlds variable int.
///
/// This trait is more of a convenience to allow writing `let data = buff.unpack()?;`
pub trait UnPackTwInt: Read {
    /// Unpack this reader holding a teeworlds variable int to a i32.
    /// # Errors
    /// Returns `Err` if there is an error reading from `Self`
    fn unpack(&mut self) -> Result<i32>;
}

impl<T: Read + ?Sized> UnPackTwInt for T {
    #[inline]
    fn unpack(&mut self) -> Result<i32> {
        unpack(self)
    }
}

#[cfg(test)]
mod tests {
    use std::io::Cursor;

    use super::*;

    #[test]
    pub fn unpack_0() {
        let mut buff = Cursor::new([0; 1]);
        assert!(pack(&mut buff, 0).is_ok());
        buff.set_position(0);
        assert_eq!(0, unpack(&mut buff).unwrap());
    }

    #[test]
    pub fn pack_0() {
        let mut buff = Cursor::new([0; 1]);
        assert!(pack(&mut buff, 0).is_ok());
        let buff = buff.into_inner();
        assert_eq!(buff[0], 0b0000_0000);
    }

    #[test]
    pub fn pack_1() {
        let mut buff = Cursor::new([0; 1]);
        assert!(pack(&mut buff, 1).is_ok());
        let buff = buff.into_inner();
        assert_eq!(buff[0], 0b0000_0001);
    }

    #[test]
    pub fn unpack_1() {
        let mut buff = Cursor::new([0; 1]);
        assert!(pack(&mut buff, 1).is_ok());
        buff.set_position(0);
        assert_eq!(1, unpack(&mut buff).unwrap());
    }

    #[test]
    pub fn pack_2() {
        let mut buff = Cursor::new([0; 1]);
        assert!(pack(&mut buff, 2).is_ok());
        let buff = buff.into_inner();
        assert_eq!(buff[0], 0b0000_0010);
    }

    #[test]
    pub fn unpack_2() {
        let mut buff = Cursor::new([0; 1]);
        assert!(pack(&mut buff, 2).is_ok());
        buff.set_position(0);
        assert_eq!(2, unpack(&mut buff).unwrap());
    }

    #[test]
    pub fn pack_minus_2() {
        let mut buff = Cursor::new([0; 1]);
        assert!(pack(&mut buff, -2).is_ok());
        let buff = buff.into_inner();
        assert_eq!(buff[0], 0b0100_0001);
    }

    #[test]
    pub fn unpack_minus_2() {
        let mut buff = Cursor::new([0; 1]);
        assert!(pack(&mut buff, -2).is_ok());
        buff.set_position(0);
        assert_eq!(-2, unpack(&mut buff).unwrap());
    }

    #[test]
    pub fn pack_minus_1() {
        let mut buff = Cursor::new([0; 1]);
        assert!(pack(&mut buff, -1).is_ok());
        let buff = buff.into_inner();
        assert_eq!(buff[0], 0b0100_0000);
    }

    #[test]
    pub fn unpack_minus_1() {
        let mut buff = Cursor::new([0; 1]);
        assert!(pack(&mut buff, -1).is_ok());
        buff.set_position(0);
        assert_eq!(-1, unpack(&mut buff).unwrap());
    }

    #[test]
    pub fn pack_0_to_63() {
        for i in 0..64 {
            let mut buff = Cursor::new([0; 1]);
            assert!(pack(&mut buff, i).is_ok());
            let buff = buff.into_inner();
            assert_eq!(i32::from(buff[0]), i);
        }
    }

    #[test]
    pub fn unpack_0_to_63() {
        for i in 0..64 {
            let mut buff = Cursor::new([0; 1]);
            assert!(pack(&mut buff, i).is_ok());
            buff.set_position(0);
            assert_eq!(i, unpack(&mut buff).unwrap());
        }
    }

    #[test]
    pub fn pack_64() {
        let mut buff = Cursor::new([0; 2]);
        assert!(pack(&mut buff, 64).is_ok());
        let buff = buff.into_inner();
        assert_eq!(buff[0], 0b1000_0000);
        assert_eq!(buff[1], 0b0000_0001);
    }

    #[test]
    pub fn unpack_64() {
        let mut buff = Cursor::new([0; 2]);
        assert!(pack(&mut buff, 64).is_ok());
        buff.set_position(0);
        assert_eq!(64, unpack(&mut buff).unwrap());
    }

    #[test]
    pub fn pack_64_trait() {
        let mut buff = Cursor::new([0; 2]);
        assert!(64.pack(&mut buff).is_ok());
        let buff = buff.into_inner();
        assert_eq!(buff[0], 0b1000_0000);
        assert_eq!(buff[1], 0b0000_0001);
    }

    #[test]
    pub fn pack_64_trait_slice() {
        let mut buff = [0; 2];
        assert!(64.pack(&mut buff.as_mut_slice()).is_ok());
        assert_eq!(buff[0], 0b1000_0000);
        assert_eq!(buff[1], 0b0000_0001);
    }

    #[test]
    pub fn unpack_64_trait() {
        let mut buff = Cursor::new([0b1000_0000, 0b0000_0001]);
        let result = buff.unpack().unwrap();
        assert_eq!(result, 64);
    }

    #[test]
    pub fn unpack_64_trait_slice() {
        let buff = [0b1000_0000, 0b0000_0001];
        let result = buff.as_slice().unpack().unwrap();
        assert_eq!(result, 64);
    }

    #[test]
    pub fn roundtrip_256_trait() {
        let mut buff = Cursor::new([0; MAX_BYTES_PACKED]);
        256.pack(&mut buff).unwrap();
        buff.set_position(0);

        let result = buff.unpack().unwrap();
        assert_eq!(256, result);
    }

    static DATA: [i32; 14] = [
        0,
        1,
        -1,
        32,
        64,
        256,
        -512,
        12345,
        -123_456,
        1_234_567,
        12_345_678,
        123_456_789,
        2_147_483_647,
        (-2_147_483_647 - 1),
    ];
    static SIZES: [u64; 14] = [1, 1, 1, 1, 2, 2, 2, 3, 3, 4, 4, 4, 5, 5];

    #[test]
    pub fn roundtrip_pack_unpack() {
        for i in 0..DATA.len() {
            let mut buff = Cursor::new([0; MAX_BYTES_PACKED]);
            DATA[i].pack(&mut buff).unwrap();
            assert_eq!(buff.position(), SIZES[i]);
            buff.set_position(0);

            let result = buff.unpack().unwrap();
            assert_eq!(buff.position(), SIZES[i]);
            assert_eq!(DATA[i], result);
        }
    }
}
