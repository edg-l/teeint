//! A teeworlds variable integer packer/unpacker.
//! [![Version](https://img.shields.io/crates/v/teeint)](https://crates.io/crates/teeint)
//! [![Downloads](https://img.shields.io/crates/d/teeint)](https://crates.io/crates/teeint)
//! [![License](https://img.shields.io/crates/l/teeint)](https://crates.io/crates/teeint)
//! ![Rust](https://github.com/edg-l/teeint/workflows/Rust/badge.svg)
//! [![Docs](https://docs.rs/teeint/badge.svg)](https://docs.rs/teeint)
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
//! Or using the trait [PackTwInt]:
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
//! Or using the trait [UnPackTwInt]:
//! ```
//! use teeint::UnPackTwInt;
//!
//! let buff = [0b1000_0000, 0b0000_0001];
//! let result = buff.as_slice().unpack().unwrap();
//! assert_eq!(result, 64);
//! ```

#![forbid(unsafe_code)]
#![deny(missing_docs)]

use std::io::{Read, Result, Write};

/// Pack a i32 into a teeworlds variable integer.
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
    current_byte |= (value & 0b0011_1111) as u8;
    value >>= 6;

    while value != 0 {
        // We have more data, set BIT_EXTEND
        current_byte |= 0b1000_0000;
        dst.write_all(std::slice::from_ref(&current_byte))?;
        // Write the BITS[7]
        current_byte = value as u8 & 0b0111_1111;
        // Discard them.
        value >>= 7;
    }

    dst.write_all(std::slice::from_ref(&current_byte))?;

    Ok(())
}

/// Unpack a teeworlds variable int from the provided reader.
pub fn unpack<T: Read + ?Sized>(src: &mut T) -> Result<i32> {
    // Adapted from https://github.com/ddnet/ddnet/blob/79df5893ff26fa75d67e46f99e58f75b739ac362/src/engine/shared/compression.cpp#L10
    let mut result: i32;
    let mut current_byte: u8 = 0;

    src.read_exact(std::slice::from_mut(&mut current_byte))?;
    let sign = (current_byte >> 6) & 1;
    result = (current_byte & 0x3F) as i32;

    const MASKS: [u8; 4] = [0x7F, 0x7F, 0x7F, 0x0F];
    const SHIFTS: [u8; 4] = [6, 6 + 7, 6 + 7 + 7, 6 + 7 + 7 + 7];

    for (mask, shift) in MASKS.into_iter().zip(SHIFTS.into_iter()) {
        if (current_byte & 0x80) == 0 {
            break;
        }

        src.read_exact(std::slice::from_mut(&mut current_byte))?;
        result |= ((current_byte & mask) << shift) as i32;
    }

    result ^= -(sign as i32);

    Ok(result)
}

/// Trait implemented by values that can be packed to a teeworlds variable int.
///
/// Note that teeworlds only packs i32 values.
///
/// This trait is more of a convenience to allow writing `0i32.pack(&mut buff)`
pub trait PackTwInt {
    /// Pack this value into a teeworlds variable int.
    fn pack<T: Write + ?Sized>(self, dst: &mut T) -> Result<()>;
}

impl PackTwInt for i32 {
    fn pack<T: Write + ?Sized>(self, dst: &mut T) -> Result<()> {
        pack(dst, self)
    }
}

/// Trait implemented by buffers holding a teeworlds variable int.
///
/// This trait is more of a convenience to allow writing `let data = buff.unpack()?;`
pub trait UnPackTwInt: Read {
    /// Unpack this reader holding a teeworlds variable int to a i32.
    fn unpack(&mut self) -> Result<i32>;
}

impl<T: Read + ?Sized> UnPackTwInt for T {
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
            assert_eq!(buff[0] as i32, i);
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
}
