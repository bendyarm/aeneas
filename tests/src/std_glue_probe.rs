//@ skip
// Standard-library code that is generic over closures and trait bounds, taken
// from the library's own source instead of a hand-written model.  (The skip
// directive keeps this out of the default runners; the generated book and
// its proofs ARE part of the certified suite:
// tests/acl2/std_glue_probe{,-proofs}.lisp.)
//
// Charon keeps the functions of other crates opaque unless asked:
// `--include <pattern>` makes one transparent (STD_GLUE in
// tests/acl2/Makefile lists the patterns used here).  The backend then
// prints it like a function of this crate -- once per trait instance it is
// used at, if it calls through a bound (see traits_probe.rs):
//
//   o.map(|x| x.wrapping_add(k))   core's Option::map, at the closure:
//                                  core-option-core-option-option-t-map[std-glue-probe-add-to-closure]
//   x.into()                       the blanket impl<T, U: From<T>> Into<U> for T,
//                                  at From<u8> for u64 -- itself from source, a cast
//   a == b on two &u32             the impl of PartialEq for references, at u32
//
// What limits this is Aeneas, function by function: each included body has
// to be code Aeneas translates, and must not close a cycle between a
// function and a trait impl.  Two that were tried and are NOT here:
// Result::unwrap_or (Aeneas: "There should be no bottoms in the value"), and
// core::cmp::max with the integers' Ord::max (a function mutually recursive
// with a trait impl, which Aeneas rejects for the whole crate).

// ---- Option and Result, with closures ----

pub fn add_to(o: Option<u32>, k: u32) -> Option<u32> {
    o.map(|x| x.wrapping_add(k))
}

// a closure that returns an Option
pub fn half(o: Option<u32>) -> Option<u32> {
    o.and_then(|x| if x % 2 == 0 { Some(x / 2) } else { None })
}

pub fn or_k(o: Option<u32>, k: u32) -> u32 {
    o.map_or(k, |x| x.wrapping_mul(2))
}

// a closure without arguments
pub fn or_else(o: Option<u32>, k: u32) -> u32 {
    o.unwrap_or_else(|| k.wrapping_add(1))
}

pub fn res_map(r: Result<u32, u8>, k: u32) -> Result<u32, u8> {
    r.map(|x| x ^ k)
}

// ---- no closure, no bound: one function each, as for any generic code ----

pub fn or_zero(o: Option<u32>) -> u32 {
    o.unwrap_or(0)
}

pub fn has(o: &Option<u32>) -> bool {
    o.is_some()
}

pub fn need(o: Option<u32>) -> Result<u32, u8> {
    o.ok_or(7)
}

// ---- conversions: the blanket Into, over From ----

pub fn widen<T: Into<u64>>(x: T) -> u64 {
    x.into()
}

pub fn widen_sum(a: u8, b: u16, c: u32) -> u64 {
    widen(a) + widen(b) + widen(c)
}

// ---- equality of references ----

pub fn same_ref<T: PartialEq>(a: &T, b: &T) -> bool {
    a == b
}

pub fn same_u32(a: u32, b: u32) -> bool {
    same_ref(&a, &b)
}

// ---- the uses ----

fn get(o: Option<u32>) -> u32 {
    match o {
        Some(v) => v,
        None => 1000,
    }
}

pub fn driver() -> u64 {
    let a = get(add_to(Some(40), 2)); // 42
    let b = get(add_to(None, 2)); // 1000
    let c = get(half(Some(10))) + get(half(Some(7))); // 5 + 1000
    let d = or_k(Some(4), 9) + or_k(None, 9); // 8 + 9
    let e = or_else(None, 6) + or_zero(None); // 7 + 0
    let f = if has(&Some(1)) && !has(&None) { 1 } else { 0 }; // 1
    let g = match need(None) {
        Ok(v) => v,
        Err(e) => e as u32,
    }; // 7
    let h = match res_map(Ok(12), 10) {
        Ok(v) => v,
        Err(_) => 0,
    }; // 6
    let i = if same_u32(3, 3) && !same_u32(3, 4) { 1 } else { 0 }; // 1
    widen_sum(1, 2, 3) + widen(a + b + c + d + e + f + g + h + i) // 6 + 2086
}
