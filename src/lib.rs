//! A teeworlds variable integer packer/unpacker.
//!
//! Packing:
//!
//! ```
//! use std::io::Cursor;
//!
//! let mut buff = Cursor::new([0; 2]);
//! assert!(teeint::pack(&mut buff, 64).is_ok());
//! let buff = buff.into_inner();
//! assert_eq!(buff[0], 0b1000_0000);
//! assert_eq!(buff[1], 0b0000_0001);
//! ```
//!
//! Or using the trait [[PackTwInt]]:
//! ```
//! use std::io::Cursor;
//! use teeint::PackTwInt;
//!
//! let mut buff = Cursor::new([0; 2]);
//! assert!(64.pack(&mut buff).is_ok());
//! let buff = buff.into_inner();
//! assert_eq!(buff[0], 0b1000_0000);
//! assert_eq!(buff[1], 0b0000_0001);
//! ```

use std::io::{Result, Write};

/// Pack a i32 into a teeworlds variable integer.
pub fn pack(dst: &mut impl Write, mut value: i32) -> Result<()> {
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
        dst.write(&[current_byte])?;
        // Write the BITS[7]
        current_byte = value as u8 & 0b0111_1111;
        // Discard them.
        value >>= 7;
    }

    dst.write(&[current_byte])?;

    Ok(())
}

/// Trait implemented by values that can be packed to a teeworlds variable int.
///
/// Note that teeworlds only packs i32 values.
///
/// This trait is more of a convenience to allow writing `0i32.pack(&mut buff)`
pub trait PackTwInt: Copy {
    /// Pack this value into a teeworlds variable int.
    fn pack(self, dst: &mut impl Write) -> Result<()>;
}

impl PackTwInt for i32 {
    fn pack(self, dst: &mut impl Write) -> Result<()> {
        pack(dst, self)
    }
}

#[cfg(test)]
mod tests {
    use std::io::Cursor;

    use super::*;

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
    pub fn pack_2() {
        let mut buff = Cursor::new([0; 1]);
        assert!(pack(&mut buff, 2).is_ok());
        let buff = buff.into_inner();
        assert_eq!(buff[0], 0b0000_0010);
    }

    #[test]
    pub fn pack_minus_2() {
        let mut buff = Cursor::new([0; 1]);
        assert!(pack(&mut buff, -2).is_ok());
        let buff = buff.into_inner();
        assert_eq!(buff[0], 0b0100_0001);
    }

    #[test]
    pub fn pack_minus_1() {
        let mut buff = Cursor::new([0; 1]);
        assert!(pack(&mut buff, -1).is_ok());
        let buff = buff.into_inner();
        assert_eq!(buff[0], 0b0100_0000);
    }

    #[test]
    pub fn pack_0_to_63() {
        for i in 0..64 {
            let mut buff = Cursor::new([0; 1]);
            assert!(pack(&mut buff, i as i32).is_ok());
            let buff = buff.into_inner();
            assert_eq!(buff[0], i);
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
}
