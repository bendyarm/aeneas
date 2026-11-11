//@ skip
// Trait-generic code.  (The skip directive keeps this out of the default
// runners; the generated book and its proofs ARE part of the certified suite:
// tests/acl2/traits_probe{,-proofs}.lisp.)
//
// A trait bound is a function-valued parameter in disguise -- `total` below
// calls whatever `area` its caller picks -- and ACL2 functions are first
// order.  So the backend prints a function that calls through one of its
// trait bounds once per INSTANCE of the bound the crate uses it at, with the
// calls resolved to the functions of the impl:
//
//   total(&Sq(2), &Rect(2, 3))   calls   traits-probe-total[traits-probe-sq][traits-probe-rect]
//
// one bracket per bound, each naming the type the impl is for.  Types are
// still erased and const generics are still parameters: only trait instances
// are specialized.  A bound that no code calls through (`T: Copy`) costs
// nothing: `first` is one function.  A closure is a struct of its captures
// with impls of Fn / FnMut / FnOnce, so higher-order functions come out the
// same way.
//
// What is NOT here, because the backend does not handle it yet: mutually
// recursive trait-generic functions; an impl method that reaches itself
// through a generic function; a modeled std function, or a method of an impl
// with const generic parameters, called through a bound (so no `for` loop
// over a generic iterator); an associated constant that depends on the
// bounds of its impl; a closure that mutates what it captures.

use std::ops::{Add, Mul};

pub trait Shape {
    fn area(&self) -> u32;
    // a provided method
    fn double_area(&self) -> u32 {
        self.area() * 2
    }
}

pub struct Sq(pub u32);
pub struct Rect(pub u32, pub u32);

impl Shape for Sq {
    fn area(&self) -> u32 {
        self.0 * self.0
    }
}

// overrides the provided method
impl Shape for Rect {
    fn area(&self) -> u32 {
        self.0 * self.1
    }
    fn double_area(&self) -> u32 {
        2 * self.0 * self.1
    }
}

// an impl with a trait bound of its own
pub struct Two<S>(pub S, pub S);

impl<S: Shape> Shape for Two<S> {
    fn area(&self) -> u32 {
        self.0.area() + self.1.area()
    }
}

// ---- calls through a bound ----

pub fn total<S: Shape, T: Shape>(s: &S, t: &T) -> u32 {
    s.area() + t.double_area()
}

// bounds handed on to another generic function, in both orders
pub fn total_both_ways<S: Shape, T: Shape>(s: &S, t: &T) -> u32 {
    total(s, t) + total(t, s)
}

// a loop at an instance
pub fn sum_areas<S: Shape>(xs: &[S]) -> u32 {
    let mut t = 0u32;
    let mut i = 0;
    while i < xs.len() {
        t += xs[i].area();
        i += 1;
    }
    t
}

// recursion at an instance
pub fn pow_area<S: Shape>(s: &S, n: u32) -> u32 {
    if n == 0 {
        1
    } else {
        s.area() * pow_area(s, n - 1)
    }
}

// a const generic next to a bound
pub fn sum_all<S: Shape, const N: usize>(xs: &[S; N]) -> u32 {
    let mut t = 0u32;
    let mut i = 0;
    while i < N {
        t += xs[i].area();
        i += 1;
    }
    t
}

// ---- a supertrait, an associated constant ----

pub trait Named: Shape {
    const ID: u32;
    fn id_plus_area(&self) -> u32 {
        Self::ID + self.area()
    }
}

impl Named for Sq {
    const ID: u32 = 7;
}

pub fn via_super<N: Named>(n: &N) -> u32 {
    n.area() + n.id_plus_area()
}

// ---- a trait with a type parameter and an associated type; a bound on the
// associated type; an associated function without `self` ----

pub trait Scale<K> {
    type Out;
    fn scale(&self, k: K) -> Self::Out;
}

impl Scale<u32> for Sq {
    type Out = Rect;
    fn scale(&self, k: u32) -> Rect {
        Rect(self.0, self.0 * k)
    }
}

pub fn scaled_area<T: Scale<u32>>(x: &T) -> u32
where
    T::Out: Shape,
{
    x.scale(3).area()
}

pub trait Unit {
    fn unit() -> Self;
}

impl Unit for Sq {
    fn unit() -> Sq {
        Sq(1)
    }
}

pub fn unit_area<T: Unit + Shape>() -> u32 {
    T::unit().area()
}

// ---- a blanket impl ----

pub trait Describe {
    fn describe(&self) -> u32;
}

impl<T: Shape> Describe for T {
    fn describe(&self) -> u32 {
        self.area() + 100
    }
}

pub fn describe_it<D: Describe>(d: &D) -> u32 {
    d.describe()
}

// ---- a trait method with a trait bound of its own ----

pub trait Visitor {
    fn visit<S: Shape>(&self, s: &S) -> u32;
}

pub struct Doubler;

impl Visitor for Doubler {
    fn visit<S: Shape>(&self, s: &S) -> u32 {
        s.double_area()
    }
}

pub fn visit_both<V: Visitor>(v: &V) -> u32 {
    v.visit(&Sq(2)) + v.visit(&Rect(1, 2))
}

// ---- closures ----

pub fn apply<F: Fn(u32) -> u32>(f: F, x: u32) -> u32 {
    f(x)
}

pub fn apply_twice<F: Fn(u32) -> u32>(f: &F, x: u32) -> u32 {
    f(f(x))
}

pub fn apply_once<F: FnOnce(u32) -> u32>(f: F, x: u32) -> u32 {
    f(x)
}

// a closure kept in a struct
pub struct Mapper<F> {
    pub f: F,
}

impl<F: Fn(u32) -> u32> Mapper<F> {
    pub fn run(&self, x: u32) -> u32 {
        (self.f)(x)
    }
}

// ---- the operators, comparisons and clone of the integer types, through a
// bound: the std impls are the primitives ----

pub fn mul_add<T: Mul<Output = T> + Add<Output = T> + Copy>(a: T, b: T) -> T {
    a * b + a
}

pub fn max_gen<T: PartialOrd + Copy>(a: T, b: T) -> T {
    if a > b {
        a
    } else {
        b
    }
}

pub fn same<T: PartialEq>(a: &T, b: &T) -> bool {
    *a == *b
}

pub fn dup<T: Clone>(a: &T) -> (T, T) {
    (a.clone(), a.clone())
}

// ---- a bound no code calls through: one function, as for a plain type
// parameter ----

pub fn first<T: Copy>(xs: &[T; 2]) -> T {
    xs[0]
}

// ---- used at no instance in this crate: there is nothing to print ----

pub fn unused<S: Shape>(s: &S) -> u32 {
    s.area()
}

// ---- the uses ----

pub fn shapes() -> u32 {
    let a = total(&Sq(2), &Rect(2, 3)); // 4 + 12
    let b = total(&Two(Sq(1), Sq(2)), &Sq(3)); // 5 + 18
    let c = total_both_ways(&Sq(1), &Rect(1, 2)); // (1 + 4) + (2 + 2)
    let d = Sq(3).double_area(); // 18: a provided method, called directly
    // a provided method at an impl that is itself at an instance: 2 * (2 + 5)
    let e = Two(Two(Sq(1), Sq(1)), Two(Sq(1), Sq(2))).double_area();
    a + b + c + d + e // 16 + 23 + 9 + 18 + 14
}

pub fn loops() -> u32 {
    let a = sum_areas(&[Sq(1), Sq(2), Sq(3)]); // 14
    let b = sum_areas(&[Rect(1, 2), Rect(3, 4)]); // 14
    let c = pow_area(&Rect(1, 2), 3); // 8
    let d = sum_all(&[Sq(1), Sq(2)]); // 5
    a + b + c + d
}

pub fn traits() -> u32 {
    let a = via_super(&Sq(2)); // 4 + (7 + 4)
    let b = scaled_area(&Sq(2)); // Rect(2, 6): 12
    let c = unit_area::<Sq>(); // 1
    let d = describe_it(&Sq(3)); // 109
    let e = visit_both(&Doubler); // 8 + 4
    a + b + c + d + e
}

pub fn closures(k: u32) -> u32 {
    let a = apply(|x| x.wrapping_add(k), 1); // 1 + k
    let b = apply_twice(&|x| x.wrapping_mul(3), 2); // 18
    let c = apply_once(move |x| x.wrapping_sub(k), 10); // 10 - k
    let d = Mapper { f: |x| x ^ k }.run(5); // 5 ^ k
    a.wrapping_add(b).wrapping_add(c).wrapping_add(d) // 29 + (5 ^ k)
}

pub fn std_impls() -> u32 {
    let a = mul_add(2u32, 5u32); // 12
    let b = mul_add(2u64, 5u64) as u32; // 12, at another instance
    let c = max_gen(3u32, 9u32); // 9
    let d = if same(&4u8, &4u8) { 1 } else { 0 }; // 1
    let (p, q) = dup(&7u32); // 7, 7
    let e = first(&[3u32, 4]); // 3
    a + b + c + d + p + q + e
}

pub fn driver() -> u32 {
    shapes() + loops() + traits() + std_impls() // 80 + 41 + 149 + 51
}
