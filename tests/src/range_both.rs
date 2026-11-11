//! Range<usize> and Range<i32> in one crate.  (Under monomorphization the two
//! instances collided in the reference backends' name registration; in the
//! polymorphic pipeline they are one declaration, and this crate checks that
//! the one Range model serves both.)
pub fn sum_usize(a: [u32; 4]) -> u32 {
    let mut acc: u32 = 0;
    for i in 0..4usize {
        acc = acc.wrapping_add(a[i]);
    }
    acc
}
pub fn count_i32() -> i32 {
    let mut acc: i32 = 0;
    for j in 1..5 {
        acc += j;
    }
    acc
}
