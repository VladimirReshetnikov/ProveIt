//! Small dependency-free utilities: a fast hasher, a union-find, arithmetic
//! modulo the Mersenne prime 2^61 - 1, and an unsigned big integer that only
//! needs multiplication by a machine word, addition and decimal printing.

use std::collections::{HashMap, HashSet};
use std::hash::{BuildHasherDefault, Hasher};

/// Fx-style multiplicative hasher (the algorithm used inside rustc).  The keys
/// here are small integers and short integer vectors, so SipHash would dominate
/// the run time of the scanner.
#[derive(Default, Clone, Copy)]
pub struct FxHasher {
    hash: u64,
}

const SEED: u64 = 0x51_7c_c1_b7_27_22_0a_95;

impl FxHasher {
    #[inline]
    fn add(&mut self, word: u64) {
        self.hash = (self.hash.rotate_left(5) ^ word).wrapping_mul(SEED);
    }
}

impl Hasher for FxHasher {
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        let mut chunks = bytes.chunks_exact(8);
        for c in &mut chunks {
            self.add(u64::from_le_bytes(c.try_into().unwrap()));
        }
        let rest = chunks.remainder();
        if !rest.is_empty() {
            let mut buf = [0u8; 8];
            buf[..rest.len()].copy_from_slice(rest);
            self.add(u64::from_le_bytes(buf));
        }
    }
    #[inline]
    fn write_u8(&mut self, i: u8) {
        self.add(i as u64);
    }
    #[inline]
    fn write_u16(&mut self, i: u16) {
        self.add(i as u64);
    }
    #[inline]
    fn write_u32(&mut self, i: u32) {
        self.add(i as u64);
    }
    #[inline]
    fn write_u64(&mut self, i: u64) {
        self.add(i);
    }
    #[inline]
    fn write_usize(&mut self, i: usize) {
        self.add(i as u64);
    }
    #[inline]
    fn finish(&self) -> u64 {
        self.hash
    }
}

pub type FxBuild = BuildHasherDefault<FxHasher>;
pub type FxMap<K, V> = HashMap<K, V, FxBuild>;
pub type FxSet<K> = HashSet<K, FxBuild>;

pub struct Dsu {
    parent: Vec<u32>,
}

impl Dsu {
    pub fn new(n: usize) -> Self {
        Dsu { parent: (0..n as u32).collect() }
    }
    pub fn find(&mut self, x: usize) -> usize {
        let mut root = x;
        while self.parent[root] as usize != root {
            root = self.parent[root] as usize;
        }
        let mut cur = x;
        while self.parent[cur] as usize != root {
            let next = self.parent[cur] as usize;
            self.parent[cur] = root as u32;
            cur = next;
        }
        root
    }
    pub fn union(&mut self, a: usize, b: usize) {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra != rb {
            self.parent[ra] = rb as u32;
        }
    }
}

pub const P61: u64 = (1u64 << 61) - 1;

#[inline]
pub fn mulmod(a: u64, b: u64) -> u64 {
    let z = (a as u128) * (b as u128);
    let lo = (z as u64) & P61;
    let hi = (z >> 61) as u64;
    let mut s = lo + hi;
    if s >= P61 {
        s -= P61;
    }
    s
}

#[inline]
pub fn addmod(a: u64, b: u64) -> u64 {
    let s = a + b;
    if s >= P61 { s - P61 } else { s }
}

#[inline]
pub fn submod(a: u64, b: u64) -> u64 {
    if a >= b { a - b } else { a + P61 - b }
}

pub fn powmod(mut base: u64, mut exp: u64) -> u64 {
    let mut result = 1u64;
    base %= P61;
    while exp > 0 {
        if exp & 1 == 1 {
            result = mulmod(result, base);
        }
        base = mulmod(base, base);
        exp >>= 1;
    }
    result
}

pub fn invmod(a: u64) -> u64 {
    powmod(a, P61 - 2)
}

/// Unsigned big integer in base 10^9 (little endian).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct BigUint(Vec<u32>);

const BASE: u64 = 1_000_000_000;

impl BigUint {
    pub fn from_u64(mut v: u64) -> Self {
        let mut digits = Vec::new();
        while v > 0 {
            digits.push((v % BASE) as u32);
            v /= BASE;
        }
        BigUint(digits)
    }
    pub fn is_zero(&self) -> bool {
        self.0.is_empty()
    }
    pub fn mul_small(&self, m: u64) -> Self {
        if m == 0 || self.is_zero() {
            return BigUint(Vec::new());
        }
        let mut out = Vec::with_capacity(self.0.len() + 3);
        let mut carry: u128 = 0;
        for &d in &self.0 {
            let cur = (d as u128) * (m as u128) + carry;
            out.push((cur % BASE as u128) as u32);
            carry = cur / BASE as u128;
        }
        while carry > 0 {
            out.push((carry % BASE as u128) as u32);
            carry /= BASE as u128;
        }
        BigUint(out)
    }
    pub fn add(&self, other: &BigUint) -> Self {
        let mut out = Vec::with_capacity(self.0.len().max(other.0.len()) + 1);
        let mut carry = 0u64;
        for i in 0..self.0.len().max(other.0.len()) {
            let s = *self.0.get(i).unwrap_or(&0) as u64 + *other.0.get(i).unwrap_or(&0) as u64 + carry;
            out.push((s % BASE) as u32);
            carry = s / BASE;
        }
        if carry > 0 {
            out.push(carry as u32);
        }
        BigUint(out)
    }
}

impl std::fmt::Display for BigUint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0.last() {
            None => write!(f, "0"),
            Some(top) => {
                write!(f, "{}", top)?;
                for d in self.0.iter().rev().skip(1) {
                    write!(f, "{:09}", d)?;
                }
                Ok(())
            }
        }
    }
}
