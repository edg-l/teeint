# teeint

A teeworlds variable integer packer/unpacker.
[![Version](https://img.shields.io/crates/v/teeint)](https://crates.io/crates/teeint)
[![Downloads](https://img.shields.io/crates/d/teeint)](https://crates.io/crates/teeint)
[![License](https://img.shields.io/crates/l/teeint)](https://crates.io/crates/teeint)
![Rust](https://github.com/edg-l/teeint/workflows/Rust/badge.svg)
[![Docs](https://docs.rs/teeint/badge.svg)](https://docs.rs/teeint)

### Packing

```rust
use std::io::Cursor;

let mut buff = Cursor::new([0; 2]);

teeint::pack(&mut buff, 64).unwrap();

let buff = buff.into_inner();
assert_eq!(buff[0], 0b1000_0000);
assert_eq!(buff[1], 0b0000_0001);
```

Or using the trait [PackTwInt]:
```rust
use std::io::Cursor;
use teeint::PackTwInt;

let mut buff = Cursor::new([0; 2]);

64.pack(&mut buff).unwrap();

let buff = buff.into_inner();
assert_eq!(buff[0], 0b1000_0000);
assert_eq!(buff[1], 0b0000_0001);
```

Or
```rust
use teeint::PackTwInt;

let mut buff = [0; 2];
64.pack(&mut buff.as_mut_slice()).unwrap();
assert_eq!(buff[0], 0b1000_0000);
assert_eq!(buff[1], 0b0000_0001);
```

### Unpacking
```rust
use std::io::Cursor;

let mut buff = Cursor::new([0b1000_0000, 0b0000_0001]);
let data = teeint::unpack(&mut buff).unwrap();
assert_eq!(data, 64);
```

Or using the trait [UnPackTwInt]:
```rust
use teeint::UnPackTwInt;

let buff = [0b1000_0000, 0b0000_0001];
let result = buff.as_slice().unpack().unwrap();
assert_eq!(result, 64);
```

License: MIT OR Apache-2.0
