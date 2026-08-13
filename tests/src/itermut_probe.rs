//@ skip
// Roadmap item 8 REPRODUCER (does not extract yet -- kept out of the runners
// via the skip directive above; not part of the certified suite).
//
// Slice iterator extraction (iter / iter_mut / zip), the last structural
// de-sugar class in aes_fixslice_encrypt.rs.  Finding (2026-08-13):
//
//   * POLYMORPHIC pipeline (charon --preset=aeneas, NO --monomorphize):
//     Aeneas core translates ALL FOUR shapes below -- the fork has upstream's
//     slice-iterator support.  IterMut::next comes back as a clean triple
//     (elem option, advanced iter, next_back : iter -> option elem -> iter)
//     and the loop threads a COMPOSED write-back continuation; see the Lean
//     backend's output and its core.slice.iter.* library models.
//   * MONOMORPHIC pipeline (--monomorphize, REQUIRED by the ACL2 backend):
//     charon materializes region-erased borrow-carrying ADT decls
//     (core::option::Option::<&'_ mut u32> and ::<(&'_ mut u32, &'_ u32)>),
//     which Aeneas's decl-level region analysis rejects ("Expected a type
//     with regions" on RErased, RegionsHierarchy via TypesAnalysis), failing
//     the decl group, then IterMut::next's signature, then every body below.
//     Shared iter() fails the same way one level up (opaque Iter<'a,u32>
//     carries the hidden borrow).
//
// So item 8 is NOT the nested-borrow research problem: the borrow-monad
// treatment already exists in core.  It is a monomorphization gap -- either
// charon mono learns to region-parameterize instantiated decls and Aeneas's
// signature decomposition learns decl-level borrows (upstream contribution),
// or the ACL2 printer learns the poly pipeline's dictionary-passing calling
// convention.  Until one of those lands, the two upstream loops stay as the
// documented indexed-for de-sugars.
//
// Shapes:
//   p1_iter_sum    : shared iteration      for x in xs.iter() { .. }
//   p2_itermut_inc : mutable iteration     for x in xs.iter_mut() { *x = .. }
//   p3_zip_xor     : the add_round_key shape: a.iter_mut().zip(b)
//   p4_ark_exact   : verbatim upstream add_round_key text
//   driver         : known-answer composition of all four (returns 44)

type State = [u32; 8];

fn p1_iter_sum(xs: &[u32]) -> u32 {
    let mut s: u32 = 0;
    for x in xs.iter() {
        s = s.wrapping_add(*x);
    }
    s
}

fn p2_itermut_inc(xs: &mut [u32]) {
    for x in xs.iter_mut() {
        *x = x.wrapping_add(1);
    }
}

fn p3_zip_xor(a: &mut [u32], b: &[u32]) {
    for (x, y) in a.iter_mut().zip(b) {
        *x ^= y;
    }
}

fn p4_ark_exact(state: &mut State, rkey: &[u32]) {
    debug_assert_eq!(rkey.len(), 8);
    for (a, b) in state.iter_mut().zip(rkey) {
        *a ^= b;
    }
}

fn driver() -> u32 {
    let mut st: State = [1, 2, 3, 4, 5, 6, 7, 8];
    let rk: [u32; 8] = [8, 7, 6, 5, 4, 3, 2, 1];
    p2_itermut_inc(&mut st); // st = [2,3,4,5,6,7,8,9]
    p3_zip_xor(&mut st, &rk); // xor with rk
    p4_ark_exact(&mut st, &rk); // xor again: cancels
    p1_iter_sum(&st) // 2+3+4+5+6+7+8+9 = 44
}
