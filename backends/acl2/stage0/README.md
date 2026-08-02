# ACL2 backend — Stage-0 validation books

Hand-transliterations of Aeneas's generated output into ACL2, with
handwritten specs and equivalence proofs — the design-validation stage of
the ACL2 backend plan, done *before* the compiler work so the
representation choices are proof-tested. Sources of truth were the
checked-in Lean outputs (`tests/lean/Demo/Demo.lean`,
`tests/lean/NoNestedBorrows.lean`, `tests/lean/Loops.lean`).

| Book | Contents |
|---|---|
| `rust-primitives.lisp` | prototype primitives: FTY `result`/`error` (mirroring `backends/coq/Primitives.v`), `((ok x) …)` b* binder, checked u32/i32 ops + characterization rules, `massert` |
| `demo.lisp` | `mul2_add1`, `incr`, `use_mul2_add1`, `CList`/`list_nth`, `i32_id`, `loops::sum` (fuel-based recursion, measure `(nfix fuel)`) |
| `demo-proofs.lisp` | specs + equivalence theorems: total ok/overflow characterizations, `list_nth` ≡ `nth`, fuel irrelevance (two-fuel induction), `sum` loop invariant, Gauss |
| `nnb.lisp` | `no_nested_borrows.rs` slice: `Pair`/`List`/`Enum`/`Sum`, `get_max`/`is_cons`/`split_list`, and `choose` **defunctionalized** (closure tagsum + first-order apply), with the extracted unit tests as `assert-event`s |
| `nnb-proofs.lisp` | incl. `nnb-choose-back-roundtrip`: ∀-inputs proof that the defunctionalized backward function implements the `&mut` write-through semantics |

## Certifying

Requires ACL2 (tested on master 2026-08) with community books including
`centaur/fty`, `std`, `arithmetic`. With `ACL2` pointing at your image and
`cert.pl` on PATH (or invoked from `books/build/`):

```sh
cert.pl -j 4 rust-primitives demo demo-proofs nnb nnb-proofs
```

`cert.acl2` supplies the FTY portcullis. Certification takes a few seconds
total on top of the (pre-certified) community books.

## Lessons already folded into the backend design

- Recursive "meaning functions" need explicit opener rules under unrelated
  inductions (goes into the Stage-1 rule library).
- Generated `defprod`/`deftagsum` must always emit an explicit `:xvar`
  (Rust fields named `x` collide with FTY's default whole-product var).
- Crate-prefix all names from day one (`List` vs Common Lisp `LIST`).
