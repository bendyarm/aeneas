# ACL2 backend — porting notes (branch `acl2-backend`)

State of this branch: `Config.ml`, `Main.ml`, and `tests/test_runner/Backend.ml`
carry the real `Acl2` additions; `src/extract/ExtractAcl2.ml.draft` encodes the
printer design (not yet compiled — rename to `.ml` when completing it). The
build intentionally does NOT yet compile: adding the `Acl2` constructor makes
every `match … backend () …` non-exhaustive, which is the work list.

## The mechanical procedure

1. `cd src && dune build 2>&1 | head` — the OCaml compiler enumerates every
   non-exhaustive match (≈274 sites at branch time). Work through them
   file by file; each falls into one of these classes:

   | Class | What `Acl2` should do |
   |---|---|
   | Pure string choices (keywords, separators, comment syntax, file ext) | sexp-world answers: `;;` comments, `.lisp` extension, `-` separator, lowercase file names |
   | F*/Coq/HOL4-vs-Lean forks (`backend_choice`) | almost always join the F*/Coq/HOL4 arm |
   | Formatter decisions (boxes, indents, parens) | usually irrelevant for sexp output — pick the simplest arm; real printing lives in `ExtractAcl2` |
   | Backend-specific features (decreases clauses, Lean lakefile, Coq `Arguments`) | no-op for `Acl2` |
   | Semantic decisions (tuple projectors, field-name disambiguation, variant naming) | follow the plan §3.2 contract: conses for tuples, crate-prefixed UPPER-HYPHEN names, always-`:xvar` for FTY |
   | Genuinely unclear | `craise` with a "TODO: ACL2 backend" message — grep-able debt, better than a guess |

2. Complete `ExtractAcl2.ml` (the draft documents each construct's target
   form). The binder plumbing (FVar/BVar, db scopes) should mirror
   `PrintPure.ml`; the sexp layer makes everything else trivial.

3. Wire the seam in `Translate.ml`: when `backend () = Acl2`, route
   declaration groups to `ExtractAcl2` (initially bypassing the
   `ExtractBase` formatter machinery; revisit per maintainer preference —
   upstream question #3 in the tracking-issue draft).

4. Tests: `tests/acl2/` + an allowlist-driven `make test-acl2` /
   `make verify-acl2` (cert.pl), per the plan's Stage 2. `Backend.ml`
   already has the `Acl2` variant, deliberately not in `all`.

## Environment facts (Claude cloud sandbox, for CI-of-the-fork planning)

- ACL2 master builds from source in ~2 min (SBCL); the needed book subset
  certifies in ~39 min at `-j2`; certified tree ≈ 2.0 GB, ≈ 0.6 GB zstd.
- The sandbox cannot build charon (needs `nightly-2026-06-01` + rustc-dev;
  rustup dist server blocked) nor fetch opam packages (opam.ocaml.org
  blocked). GitHub itself and GitHub release assets ARE reachable.
- Consequence: to iterate on this branch inside such a sandbox, ship a
  dev-container rootfs via release assets containing: the opam switch with
  aeneas deps installed (+ dune), charon built at `charon-pin` (binary +
  charon-ml built in the switch), the pinned Rust nightly toolchain, and
  ACL2 + the certified book subset. Then the edit→`dune build`→extract→
  `cert.pl` loop runs entirely offline.

## Known workaround: unrolling loops that call heavy functions

ACL2's admission of a *recursive* (fuel) loop function whose body reaches a large
callee expands that callee during admission and can blow up super-linearly. The
extracted AES-128 key schedule first exhibited this: the `rcon` loop calls
`key_round` → `sub_bytes` (the 113-gate S-box), and the loop book took >9 minutes
to certify (and did not finish). The same shape appears for any loop that calls a
heavy function.

Two fixes, both verified:

1. **Unrolling (used in the vendored AES).** A loop with a statically-known trip
   count is written straight-line, so its extraction is non-recursive and admits
   in seconds (the encrypt/decrypt rounds and the key-schedule `rcon` loop). The
   round body stays a single shared function (`key_round`, `sub_bytes`, …), so
   there is no duplicated logic — only repeated one-line calls. Faithful only
   because the counts are static (AES-128); NOT a general solution.

2. **Principled fix (TODO in ExtractAcl2).** Emit `(in-theory (disable <callee>))`
   for heavy callees before the loop functions that call them (and, for
   backward-compatible downstream proofs, re-`enable` at end of book). Confirmed
   locally: disabling `key_round` before the `rcon` loop makes the *recursive*
   version admit in ~6s. This keeps genuine (non-static-count) loops as loops.
   Disabling a `:definition` rune does not disable its `:executable-counterpart`,
   so execution-based known-answer tests still run.

## Resolved: the `fail` runtime macro used to collide with centaur/gl

The Phase-2 bijection proof (`tests/acl2/aes_fixslice_bijection.lisp`) bit-blasts
the extracted `bitslice`/`inv_bitslice` with **centaur/gl**, so a single ACL2
world must hold both the extracted code and GL. It cannot: `rust-primitives`
defines `fail` as a *macro* (a one-line alias, `(defmacro fail (e) `(result-fail
,e))`), while centaur/gl transitively defines a *function* named `fail`
(`misc/hons-help`). ACL2 forbids a macro and a function to share a name in one
world, so `(include-book "centaur/gl/gl")` after the extracted book aborts with
"The name FAIL is in use as a macro." (`ok`, `array-index`, `u32p`, … do NOT
collide — `fail` is the only one.)

RESOLVED (principled fix landed): the printer now emits `result-fail`
directly (two sites in `ExtractAcl2.ml`), the runtime uses `result-fail`
throughout and no longer defines a `fail` macro, and the one handwritten
use (`proofs.lisp`) was updated. Every extracted book is GL-ready as
generated; the `gl-variants` Makefile rule and the two `-gl` variant
files are gone, and `aes_fixslice_bijection` includes the generated book
directly. (`ok` remains a macro — it collides with nothing.) The interim
`sed`-variant approach is preserved in the git history should another
name collision ever appear.

## AES fixslice vendoring: provenance, mechanical audit, de-vendoring roadmap

**Provenance.** `tests/src/aes_fixslice_encrypt.rs` was written BY HAND (no tool
generated it) as an adaptation of RustCrypto `aes` v0.9.1
`src/soft/fixslice32.rs` (repo `RustCrypto/block-ciphers`, tag `aes-v0.9.1`,
commit `507938c`), created in commit `c3555dd1` so the module would go through
today's Charon -> Aeneas -> ACL2 pipeline. The pristine upstream file is checked
in at `tests/src/reference/fixslice32-aes-v0.9.1.rs` (MIT/Apache-2.0) so the
adaptation is diffable forever. The theorems are about the ADAPTED copy; they
transfer to shipped RustCrypto exactly modulo the deltas below.

**Mechanical audit** (function-by-function, whitespace/comment-insensitive;
script-verified against the reference copy):

| Delta class | Functions | Nature |
|---|---|---|
| Byte-identical | `ror`, `ror_distance`, `rotate_rows_*`, `rotate_rows_and_columns_*`, `delta_swap_1/2` (10 fns), and the whole `define_mix_columns!` macro | none |
| Signature-only (`&mut [u32]` -> `&mut State`/`&[u32;88]`) | `sub_bytes` (the 113-gate S-box network: body verbatim, `debug_assert` restored), `sub_bytes_nots` (assert restored), `inv_sub_bytes` (assert restored), `add_round_constant_bit`, `xor_columns`, `inv_shift_rows_1/2/3` (no asserts upstream: thin wrappers) | zero gate changes |
| `iter_mut`/`zip` -> indexed `for` | `shift_rows_1/2/3` (asserts restored), `add_round_key` (upstream's `rkey.len()` assert has no analog until the roadmap-#7 subslice signature returns) | same ops, indexed |
| LE byte plumbing (`from_le_bytes`+`try_into` -> `ld_le`; `to_le_bytes`+`copy_from_slice` -> explicit arrays with masked `as u8` casts) | `bitslice` (both input asserts restored; the `output.len()` assert has no analog: ours returns `State` instead of taking `&mut [u32]`), `inv_bitslice` (assert restored) | endianness-explicit |
| Subslice borrows -> `(array, offset)` + `read8`/`write8`/`*_at` wrappers | `aes128_key_schedule` call sites, `sub_bytes_at` etc. (vendored-only helpers) | structural |
| Loop unrolls | encrypt/decrypt round loops (still unrolled); key-schedule rcon loop (RE-ROLLED, recursive extraction) | control flow |
| ~~`memshift32` forward-loop delta~~ RESOLVED (de-vendor pass 1): body is now VERBATIM upstream -- `for i in (0..8).rev()` restored AND both `debug_assert`s restored (they survive the charon preset and extract as `massert`s, so the certified book carries upstream's own alignment/bounds checks as hypotheses) | `memshift32` | signature-only remains (`&mut [u32; 88]` vs upstream `&mut [u32]`) |
| Dropped | `aes192_*`/`aes256_*`, cipher-crate API, `cfg(aes_backend_soft = "compact")` branches (non-compact path vendored) | scope reduction |

**De-vendoring roadmap** — what the toolchain needs so each delta can be
deleted and the audited subject moves toward verbatim upstream:

1. FREE / already zero: macros (rustc expands pre-MIR); `cfg` selection
   (rustc resolves); those deltas need no toolchain work.
2. DONE -- `debug_assert!`: the charon preset KEEPS them (they extract as
   `(massert ...)` ok-binders).  All 11 restorable asserts are restored
   verbatim: memshift32's two (pass 1) plus the nine length asserts on
   sub_bytes / sub_bytes_nots / inv_sub_bytes / shift_rows_1/2/3 /
   bitslice (input0, input1) / inv_bitslice (pass 2).  Proof impact was one
   lemma pair: sub_bytes_nots's :ok/len characterization needed only
   len >= 7 (it touches indices 0,1,5,6) but upstream's assert demands
   len == 8 exactly -- the hypothesis tightened to match, and every call
   site already reads exact-length windows.  The two upstream asserts NOT
   restored bind variables that do not exist under remaining signature
   deltas: bitslice's `output.len()` (ours returns `State` by value) and
   add_round_key's `rkey.len()` (returns with the roadmap-#7 subslice
   signature).
3. Loop re-rolls: key schedule DONE (see below); re-roll the encrypt/decrypt
   round loops the same way (`-loops-to-rec` + opaque round fns admit fine);
   requires reworking the Phase-3 round-unfold proofs to the recursive form.
   Medium, proof-side only.
4. DONE, both halves -- `Rev<Range<usize>>` support AND the `memshift32`
   source reversion that it unblocks:
   * Backend: `Iterator::rev` and `Rev::next` have real bodies when charon
     builds against a Miri-provisioned sysroot and translate as-is; WITHOUT
     that sysroot they arrive opaque, so the backend now carries fallback
     syntheses for all four leaves: `rev` and the blanket
     `IntoIterator for Rev<_>` as identity (newtype-erased: a Rev value IS
     its inner range), `Rev::next` and `Range::next_back` as the reverse
     advance.  `core::slice::len` (reached by the restored bounds assert)
     maps to `vec-len`.  Emission is now two-pass (all type groups before
     all fun/global groups): a synthesized `Rev::next` body reads the Range
     defprod's fields, a dependency charon's declaration order cannot know.
   * Source: `memshift32` reverted to VERBATIM upstream body -- `.rev()`
     loop plus both `debug_assert`s, which extract as `massert`s.  Proof
     rework (the write order flips to descending): keychain gains a
     descending spec `ms-spec-d` + step lemmas driven by `rvnext-on-range`,
     bridged to the unchanged ascending interface RHS by `ms-spec-d-is-ms-spec`
     (equal-by-nths over the disjoint windows); the interface lemma
     `memshift32-is-msspec` keeps its RHS and gains upstream's own
     `(rem src 8) = 0` hypothesis, which `rem-8i` discharges at every
     (8-aligned) schedule call site; the length-only `-len` family and the
     fuel-canon/loop-collapse lemmas in keydecomp/keyasm additionally
     thread `true-listp` (the descending<->ascending bridge needs it).
   Regression crate `tests/src/rev_range.rs` (+ known-answer proofs book)
   covers both iterator directions, including the exact upstream
   memshift32 shape, and certifies from the fallback syntheses alone.
5. `u32 as u8` narrowing casts: the runtime currently models narrowing casts as
   checked; Rust `as` truncates totally. Fix the cast primitive to truncating
   semantics; the masked-cast delta then disappears. Small, and a semantic-
   fidelity fix independent of AES.
6. `from_le_bytes`/`to_le_bytes`/`try_into`/`copy_from_slice`: add runtime
   primitives (pure LE assembly + monadic length checks) and printer mappings.
   Small-medium.
7. `&mut rkeys[a..b]` subslice borrows: Aeneas already splits these borrows;
   the backend needs the monomorphized `Index/IndexMut<Range<usize>>` ops
   (subrange read + write-back) as primitives. This deletes `read8`/`write8`/
   the `*_at` wrappers — the largest structural delta. Medium.
8. `iter_mut()`/`.zip()` over slices: needs `core::slice::IterMut` (and `Zip`)
   extraction — an Aeneas-core capability question, not just the printer.
   Probe first; possibly an upstream Aeneas contribution. Largest unknown.
9. Whole-crate extraction (cipher traits, generic-array, batch API, AES-192/256):
   long-term; today's audited claim is module-level (the fixslice32 math).

Worked so far: the key-schedule rcon loop was restored to a `for` loop and the
recursive extraction admits fast and re-certifies the whole chain including the
FIPS-197 executable checks — evidence that the "unrollings are required" caveat
was about a pipeline limitation that no longer exists for factored loop bodies.

## Resolved: extraction naming collision on mixed Range instantiations

Instantiating BOTH `Range<usize>` and `Range<i32>` in one crate (an
unannotated `for _i in 1..11` defaults to i32 when nothing constrains the
type) used to make extraction exit nonzero with "The chosen name is already
in the names set: core_ops_range_Range_t".

Root cause, found by reproduction (`tests/src/range_both.rs`): the failure
was in ExtractBase's name REGISTRATION, which Translate.ml runs for every
backend before routing to the printer.  Those names are computed through
charon-ml's pattern machinery, whose `path_elem_with_generic_args_to_pattern`
deliberately drops `PeInstantiated` elements ("patterns match the logical
structure, not the instantiation") -- correct for name MATCHING, wrong when
the same path is reused to generate extraction names for monomorphized
instances.  The ACL2 printer was never affected: it builds its own name maps
from the pretty-printed item name (which keeps `::<usize>`), and the emitted
book was already complete and correct -- only the vestigial registration
errored and failed the run.

Fork fix (landed): Translate.ml skips all five `*_register_names` folds when
the backend is Acl2; the printer's own maps are the single source of truth.
All golden books regenerate byte-identically; `range_both.rs` (+ its
known-answer proofs book) is a permanent regression test.  The `usize` loop
annotations in the vendored AES source are no longer load-bearing.

Upstream-facing fix (for the tracking issue): render `PeInstantiated`
arguments in name generation -- either a `to_pat_config` flag in charon-ml's
NameMatcher or a post-pass in aeneas's ExtractName -- so every backend gets
collision-free names under `--monomorphize`.
