//@ skip
// Generic code the ACL2 backend takes straight from polymorphic LLBC, with no
// monomorphization.  (The skip directive keeps this out of the default
// runners; the generated book and its proofs ARE part of the certified suite:
// tests/acl2/generics_probe{,-proofs}.lisp.)
//
//   type parameters   one ACL2 function serves every instantiation (ACL2
//                     functions have no type parameters to instantiate)
//   const generics    ordinary parameters: `N` is the first formal, const-n
//   tuple structs     FTY products with fields f0, f1, ...; a struct without
//                     fields is (unit)
//
// Calls through a trait bound (`fn f<T: Tr>(x: T) { x.m() }`) and closures
// are in traits_probe.rs.  What the backend does not handle yet: a function
// that returns a mutable borrow.

// a type parameter
pub fn id<T>(x: T) -> T {
    x
}

pub struct Pair<A, B> {
    pub a: A,
    pub b: B,
}

pub fn swap<A, B>(p: Pair<A, B>) -> Pair<B, A> {
    Pair { a: p.b, b: p.a }
}

// a const generic, read in a loop bound
pub fn sum_arr<const N: usize>(a: &[u32; N]) -> u32 {
    let mut s = 0u32;
    let mut i = 0;
    while i < N {
        s = s.wrapping_add(a[i]);
        i += 1;
    }
    s
}

// a const generic, used to build a value
pub fn zeros<const N: usize>() -> [u32; N] {
    [0u32; N]
}

// a const generic passed on to another function
pub fn sum_zeros<const N: usize>() -> u32 {
    sum_arr(&zeros::<N>())
}

// tuple structs, one with a single field, and a struct without fields
pub struct Rect(pub u32, pub u32);
pub struct Meters(pub u32);
pub struct Marker;

impl Rect {
    pub fn area(&self) -> u32 {
        self.0 * self.1
    }
}

pub fn widen(r: Rect, by: Meters, _m: Marker) -> Rect {
    Rect(r.0 + by.0, r.1)
}

pub fn driver() -> u32 {
    let p = swap(Pair { a: 1u32, b: 2u32 }); // Pair { a: 2, b: 1 }
    let r = widen(Rect(p.a, 3), Meters(id(4)), Marker); // Rect(6, 3)
    // 18 + 6 + 0 + 1
    r.area() + sum_arr(&[1, 2, 3]) + sum_zeros::<5>() + p.b
}
