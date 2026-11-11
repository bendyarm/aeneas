# ACL2 backend — porting notes (branch `acl2-backend`)

**Current state: see "The pipeline on `acl2-next`", "Trait-generic code" and
"Toward all Rust code" at the end.  The sections in between are the port's
log, oldest first; where they describe `--monomorphize` or the carved
pipeline they describe `acl2-backend`, not `acl2-next`.**

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

## Environment facts (Claude cloud sandbox) and the prebuilt dev environment

- The sandbox cannot build charon (needs `nightly-2026-06-01` + rustc-dev;
  rustup's dist server is blocked) nor fetch opam packages (opam.ocaml.org and
  codeload.github.com are blocked). Reachable: github.com (git), GitHub release
  assets (objects.githubusercontent.com), crates.io, and -- once allowed in the
  cloud environment's network settings -- ghcr.io together with
  pkg-containers.githubusercontent.com (GHCR redirects every blob download
  there; ghcr.io alone is not enough). Those settings belong to the
  environment, not the session, so they persist.
- Consequence: the toolchain arrives prebuilt. The first cut was the
  `aeneas-dev-v1` release of this repo (a rootfs tarball built by hand on
  2026-08-03 from a Dockerfile: opam switch with the aeneas deps, charon at
  `charon-pin`, the pinned Rust nightly, ACL2 master + a certified book
  subset). It is superseded by the `aeneas-acl2-devenv` repository
  (https://github.com/bendyarm/aeneas-acl2-devenv), whose image
  `ghcr.io/bendyarm/aeneas-acl2-dev` is built by CI from pinned commits of
  this branch and of bendyarm/charon, takes ACL2 and its certified books from
  Kestrel's `acl2-kcerts` image (which, unlike the v1 subset, includes
  centaur/gl and kestrel/crypto), and can be pulled into a sandbox without
  Docker (`scripts/bootstrap-sandbox.sh`, then `scripts/in-dev.sh`). The
  edit -> `dune build` -> extract -> `cert.pl` loop then runs offline.
- Reproduction record (2026-09-04, sandbox with 2 cores / 7 GB): starting
  from the v1 rootfs moved to this branch @ c1dcfb54 and charon @ 58b7d543,
  aeneas built in 2m22s and charon in 5m42s (the image's cargo cache is
  enough to rebuild charon offline); the AES crate extracts in about a
  minute; `make -C tests/acl2 regen` over all crates reproduces every
  generated book byte-for-byte; and all 78 books of `tests/acl2` certify
  against ACL2 @ 0612757b (kcerts, 2026-09-02) in ~16 CPU-minutes. Two
  things to know: the GL books need `cert.pl -j 1` on machines with less than
  ~12 GB (with `-j 2` on 7 GB the run died silently in the middle of a book,
  with no error in the log), and the `verify`/`regen` lists in
  `tests/acl2/Makefile` had fallen behind the directory (decrypt books,
  probes) -- fixed alongside this note.

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
| ~~Signature-only~~ RESOLVED (pass 7): `sub_bytes`/`sub_bytes_nots`/`inv_sub_bytes`, `shift_rows_*`/`inv_shift_rows_*`, `add_round_constant_bit`, `xor_columns` all take upstream's `&mut [u32]` slices (asserts restored where upstream has them; `mix_columns_*` keep upstream's own `&mut State`) | -- | none |
| ~~`iter_mut`/`zip` -> indexed `for`~~ RESOLVED (pass 10, roadmap #8): `shift_rows_1/2/3` and `add_round_key` bodies are VERBATIM upstream `iter_mut()`/`.zip()` loops; the crate extracts through charon's mono carve-out pipeline (see the Makefile recipe) with the printer's first-order iterator models | -- | none |
| ~~LE byte plumbing~~ RESOLVED (pass 8): `bitslice`/`inv_bitslice` bodies are VERBATIM upstream (`from_le_bytes`/`try_into`, `to_le_bytes`/`copy_from_slice`, out-param `bitslice` with all three asserts); `ld_le` deleted; `BatchBlocks`/`State::default()` -> array literals remain the documented de-sugar | -- | none |
| ~~Subslice borrows -> `(array, offset)` + `read8`/`write8`/`*_at` wrappers~~ RESOLVED (pass 9): `aes128_key_schedule` is verbatim upstream (`&mut rkeys[..8]`/`[off..off+8]` subslice borrows, `(8..72).step_by(32)` fold, `for i in 1..11` NOTs loop); the read8/write8/sub_bytes_at/sub_bytes_nots_at/add_rc_bit_at/inv_shift_rows_*_at/bitslice_into/add_rcon/key_round wrapper layer is DELETED | -- | none |
| ~~Loop unrolls~~ FULLY RESTORED (passes 3 + 11): the encrypt round loop (pass 3) AND the decrypt round loop (pass 11, descending rk_off) are verbatim upstream bare `loop { ... break }` text, extracted as recursive loop functions; key-schedule rcon loop re-rolled earlier | -- | none |
| ~~`memshift32` forward-loop delta~~ FULLY RESOLVED (passes 1 + 7): body verbatim upstream (`.rev()` + both `debug_assert`s, extracting as `massert`s) AND the upstream `&mut [u32]` signature | `memshift32` | none |
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
   site already reads exact-length windows.  The remaining two arrived with
   the signature reversion passes: add_round_key's `rkey.len()` (pass 7,
   with the (state, rkey: &[u32]) signature) and bitslice's `output.len()`
   (pass 8, with the out-param signature) -- ALL THIRTEEN upstream asserts
   are now present verbatim.
3. DONE for everything vendored -- loop re-rolls: key schedule (rcon + fold
   loops) and now the ENCRYPT ROUND LOOP.  The upstream shape is a bare
   `loop` over a mutated `rk_off` counter with the break in the MIDDLE of
   the body (after the mc1 quarter); it extracts as a recursive loop
   function threading (state, rk_off) with the break as an early (ok state)
   return -- no iterator machinery at all.  Proof architecture: enc-collapse
   keeps its statement; a new enc-loop-collapse proves the loop at fuel 100
   equals the nine middle rounds by THREE explicit expansions (fuel 100 at
   rk_off 8, 99 at 40, 98 at 72), with add_round_key fuel-canonicalized by
   a generic-fuel ark-form-n (the loop calls it at decremented fuels).
   Everything downstream of enc-collapse's equation is untouched.
   Regression crate `tests/src/loop_break.rs` (+ known-answer proofs book)
   pins the loop{...break} extraction shape and the expand-collapse proof
   pattern.  Pass 11 re-rolled the DECRYPT round loop the same way
   (descending `rk_off`, break at `rk_off == 0` in the middle of the
   body); `dec-loop-collapse` proves it by the same three-expansion
   pattern, and the decrypt proof stack on top of it (per-op push-ins,
   mask/frame algebra, reverse round ladder, spec hop) closes with
   DECRYPT-CORRECT: the extracted decrypt -- key schedule and inverse
   cipher -- equals `aes::aes-128-decrypt` for all keys and blocks
   (`aes_fixslice_decfinal`).
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
5. DONE -- truncating casts: every cast primitive (the def-rust-int-type
   macro family plus the hand-written u32/i32) now models Rust `as` exactly:
   total two's-complement truncation into the target range, never failing.
   New -RK (always :ok), -RANGE (result is in range) and the existing -OK
   (in-range identity) rules form the reasoning interface; the definitions
   are DISABLED by default (a total definition otherwise opens on symbolic
   arguments and spills mod/ifix arithmetic into every goal -- ground calls
   still compute via the executable counterparts).  inv_bitslice's masked
   casts `((w>>k) & 0xff) as u8` are reverted to upstream's bare
   `(w>>k) as u8`.  Known-answer asserts in rust-primitives pin the wrap
   behavior (300 as u8 = 44, 255 as i8 = -1, -1 as u32 = 2^32-1, ...).
6. DONE -- LE byte plumbing:
   runtime prims u32-from-le-bytes / u32-to-le-bytes (total, non-monadic:
   Aeneas types them pure) and slice-copy-from-slice (fails unless lengths
   agree); printer syntheses for slice.try_into() into a fixed byte array
   (constructing core's own monomorphic Result tagsum; the length is read
   off the Ok payload's array type) and Result::unwrap on it.  Validated by
   tests/src/lebytes_probe.rs + known-answer proofs incl. an LE round-trip
   theorem.  The nested write shape upstream's inv_bitslice uses --
   `output[k][o..o+4].copy_from_slice(...)`, a single-element mutable
   index wrapping a range borrow -- is also supported (CloElemBack:
   forward array-index, backward update-nth) and probe-validated
   (st2-known-answer).  The bitslice/inv_bitslice bodies are now VERBATIM
   upstream: out-param bitslice with all THREE debug_asserts (output.len()
   was the last signature-blocked assert -- all 13 upstream asserts are now
   present), from_le_bytes over try_into'd subslice reads, and
   to_le_bytes/copy_from_slice writes through the nested
   output[k][o..o+4] borrows; ld_le is DELETED.  The ~300 proof-side
   bitslice references thread the out-parameter (a (list 0 ... 0) initial
   array, fully overwritten).  GL note: the LE prims are defined via
   logior/ash/logand, NOT +/*/mod -- identical on byte inputs, but adders
   with carries blow the BDD node count (the 48-variable
   add-round-key-through-packing crux went from OOM-at-7GB to 8 seconds on
   this change alone); the explicit inv-bitslice :ok/len lemmas keep the
   window prims at their nth/len interface instead of opening take/append.
7. DONE, both sides -- subslice borrows: Aeneas
   splits `&mut a[lo..hi]` into a forward read returning a (subslice,
   backward-closure) pair, bound via an intermediate pair variable and a
   tuple-destructuring let.  The printer now: synthesizes every shared
   monomorphized `Index<RangeX<usize>>::index` to a first-order defun over
   the new vec-index-range prim (RangeTo/RangeFrom default the missing
   bound to 0 / (len a)); intercepts the mutable pair-lets, prints the
   forward read, and delegates the backward closure to data -- applying it
   prints the total vec-update-range splice (an escaping closure variable
   yields an unbound-variable certification failure, never a silent
   mistranslation).  &mut array-to-slice coercions are the identity with an
   identity backward.  vec-index-range/vec-update-range come with the
   window nth/len/true-listp interface rules.  Validated by
   tests/src/subslice_probe.rs + known-answer AND symbolic proofs.
   ENCRYPT SIDE DONE: every op now has upstream's slice signature
   (sub_bytes/sub_bytes_nots/inv_sub_bytes, shift_rows_*/inv_shift_rows_*,
   add_round_constant_bit, xor_columns, memshift32 -- closing memshift32's
   LAST delta); add_round_key has upstream's (state, rkey: &[u32])
   signature WITH its restored rkey.len() debug_assert, and the
   encrypt/decrypt call sites pass upstream's own &rkeys[..8] /
   &rkeys[rk_off..(rk_off + 8)] / &rkeys[80..] subslices.  Proof
   architecture: enc-chain and everything downstream (ladder, rounds,
   final) are UNTOUCHED -- six window lemmas rewrite each synthesized
   Index<RangeX> read composed with add_round_key straight to the old
   (arkw-spec 0 8 s rk off) form via take8-nthcdr-is-rd8 and an
   arkw-spec window-shift.  SCHEDULE SIDE DONE (pass 9), closing the class:
   * StepBy<Range<usize>> synthesis: StepBy is opaque in the LLBC, so the
     printer emits its own defprod {iter, step, first-take} and synthesizes
     the trio by name -- step_by(step) fails on step == 0 and stores
     step - 1 with first_take = t (upstream's own representation);
     into_iter is the identity; next specializes Iterator::nth to Range
     (first take yields start; afterwards jump to start + (step-1), i.e.
     advance to start + step of the previous yield; park at (end, end)
     when past the end).  Pinned by tests/src/subslice_probe.rs's
     stepby_sum probe (known-answer proof).
   * aes128_key_schedule is verbatim upstream: bitslice into
     &mut rkeys[..8], the rcon loop through &mut rkeys[off..off+8]
     subslices, the (8..72).step_by(32) inv_shift_rows fold, the trailing
     window at [72..80], and the 1..11 NOTs loop; the whole wrapper layer
     (read8/write8/*_at/bitslice_into/add_rcon/key_round) is deleted.
   * Phase-4 proof restack (the schedule now extracts as one inline
     rcon-loop body instead of a key_round function): keyround proves ONE
     LOOP-STEP EQUATION sched-loop0-step -- an iteration of the extracted
     loop0 at index c equals the pure window model kround(rkeys,off,c)
     (the old key-round-unfold's xc/w8/ms-spec tower) -- under LENGTH-ONLY
     hypotheses, so keyasm's loop collapse needs no invariant and no fuel
     canonicalization at all; kround's readers (window/len/frame-below/
     true-listp) replace the key_round interface with strictly weaker
     hypotheses (no wstate, no alignment).  keystep's step-star GL cruxes
     are stated directly over the pure krw8, so keycore's per-round GL
     cruxes over the deleted wrapper went away entirely.  The seed is the
     vec-update-range window form (defund seed).  keyasm collapses the
     three loops -- rcon by induction over sched-loop0-step, the step_by
     fold by explicit three-step expansion through the synthesized StepBy
     next (yields 8, 40, then None), the NOTs loop by the lockstep
     off = 8i induction -- into the same ks-decomp shape, and keyread/
     keymain/windows/ladder are unchanged modulo (seed key).  Two
     rule-shape lessons are recorded in the books: window arithmetic in
     left-hand sides must be a free variable pinned by an
     (equal hi (+ off 8)) hypothesis (embedded (+ off 8) patterns match
     neither ACL2's constant-first sum normal form nor evaluated
     literals), and alignment hypotheses must be stated in MOD form
     (arithmetic-5 normalizes goal-side rem to mod, and backchain relief
     does not cross that normalization).
8. MACHINERY LANDED, probe certified (was "largest unknown") --
   `iter_mut()`/`.zip()` over slices, the last structural de-sugar class
   (shift_rows_*'s per-word loop and add_round_key's iter_mut().zip()).
   Probe: tests/src/itermut_probe.rs (p1 iter / p2 iter_mut / p3 zip /
   p4 verbatim add_round_key / known-answer driver); its extraction and
   proofs are IN the certified suite (itermut_probe{,-proofs}.lisp:
   driver = (ok 44), plus elementwise symbolic theorems with free
   elements -- any slot transposition or off-by-one in the write-back
   model would be unprovable).  How it works:
   * Original finding (still the map): Aeneas CORE supports slice
     iterators on the POLYMORPHIC path; plain --monomorphize bakes
     region-erased borrow-carrying decls that decl-level region analysis
     rejects.  Nested-borrow research was never the blocker.
   * charon fork, mono carve-out (bendyarm/charon 5695c917 + d49928a2):
     under --monomorphize --monomorphize-mut=except-types (plus
     --remove-adt-clauses --lift-associated-types='*'), instantiations
     whose baking would erase unrecoverable regions stay polymorphic --
     types with lifetime args / mut-infected args / region-mentioning
     args; fns with mut-ref signatures under lifetime args; trait
     decls/impls in lockstep so dictionary witnesses stay coherent.
     Inert without --monomorphize-mut (AES extraction byte-identical).
   * aeneas InterpPaths fix (71afbe52): the place write-back check
     compared an erased against an un-erased type.
   * ACL2 printer (this commit): the opaque iterators become first-order
     models -- Iter/IterMut {lst, pos} defprods, Zip {a, b} -- with
     synthesized ctors/next (next yields (opt . iter') and advances);
     iter_mut/zip calls are intercepted at their (forward, backward)
     pair-lets (backward -> closure kinds extracting ->lst / ->a); the
     next triple's next_back becomes CloNextBack (None-application =
     identity; Some only inside wrap lambdas); and the loop's
     arrow-typed back formal is DEFUNCTIONALIZED to a list of pending
     write values: identity closure literal ~> nil, wrap lambda ~>
     (cons v back), applied by emitted -apply-back/-wb-some companions
     on the decrement model (after k nexts pos = k; applying pending
     writes latest-first lands each in the slot its next read; the
     backward pair-extraction then reads the final list out).
     Defunctionalization fires ONLY at loop-call sites; lambdas anywhere
     else keep the loud v0 skip (and a failed shape-probe restores the
     gensym counter, keeping skipped-decl output byte-identical).
   * AES flip DONE (pass 10): shift_rows_1/2/3 and add_round_key are
     verbatim upstream text (byte-compared against the pristine
     reference) and the AES crate extracts through the carved pipeline.
     Proof restack was three books, all exported statements unchanged:
     keydecomp's per-loop base/step/inductions became direct
     wrapper-level unrolls (the (:free ...) :expand hint re-fires at
     each exposed fuel; next reads the ORIGINAL list, writes pending);
     keyasm's two-fuel inductions became double unrolls (both fuel
     spines meet syntactically, (< 8 (nfix n)) deciding the symbolic
     side's zp tests); cipher's ark-loop0 lemmas became a direct
     ark-form-n unroll meeting arkw-spec under the std/lists
     update-nth commuting rules.  The GL books (addroundkey,
     shiftrows, keyschedule, keyfold) recertify UNCHANGED -- GL
     symbolically executes the new machinery.  Extraction wart, known
     and cosmetic: under the carved flags the try_into decl's mangled
     name embeds a hax name-resolution artifact
     ("...tryinto-u8-4usize-type-error-can-t-compute-self-type0-...");
     self-consistent, referenced by no handwritten book, candidate
     charon-side fix.  The panic-path Option instance also arrives
     generic (core-option-option) instead of monomorphized; it is
     referenced by nothing.
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

## The pipeline on `acl2-next`: polymorphic LLBC

`acl2-next` is `acl2-backend` (23cf8c88) merged with AeneasVerif/aeneas main
as of 2026-11-10 (0d21a9ec; charon 0.1.315, rust `nightly-2026-09-17`), with
the backend moved to the polymorphic pipeline.  Every crate is extracted the
same way:

    charon rustc --preset=aeneas --dest-file X.llbc -- [--edition=2021] X.rs ...
    aeneas -backend acl2 -use-fuel -loops-to-rec X.llbc

Stock upstream charon: no `--monomorphize`, no carve-out, no charon fork
(checked with unmodified AeneasVerif/charon at the commit this tree pins,
454586e9).  All 20 books generated on `acl2-backend` regenerate this way
with every crate function they had before, and the directory certifies (84
books, with those of `traits_probe` and `std_glue_probe` below).  (Building
needs `ppx_deriving_hash >= 0.1.5` on the OCaml side and the
`crates/minirust` submodule on the charon side.)

### Why not `--monomorphize`

Monomorphization bakes region-erased instances of borrow-carrying items
(`Option<&mut u32>`, the slice iterators) before Aeneas's borrow analysis,
which needs those regions; the carve-out in bendyarm/charon kept exactly
those items polymorphic.  In polymorphic LLBC nothing erases the regions, so
the problem does not arise: `itermut_probe`, the crate the carve-out existed
for, extracts as is.

Upstream has also moved away from the combination.  Current charon rejects
`--preset=aeneas` together with `--monomorphize` (issue #1538, PR #1539): the
preset's `--index-to-function-calls` / `--ops-to-function-calls` desugar
`a[i]`, `[x; N]` and array-to-slice coercions to calls to polymorphic std
functions, which a monomorphic run does not have (PR #1382 removed the LLBC
builtins they replace); and monomorphic mode now excludes polymorphic items
altogether (PR #1436), which is what the carve-out relied on keeping.  The
`acl2-next` branch of bendyarm/charon carries the carve-out merged onto
upstream main; it builds but is not used by anything here.

### What monomorphization was doing for the backend, and what does it now

ACL2 functions have no type parameters, so the monomorphized copies of a std
type were already identical products with `any-p` fields under different
names (`core-option-option-usize-`, `core-option-option-i32-`).  The
polymorphic pipeline has one (`core-option-option`).  What monomorphization
contributed was only the *resolution of instantiations*: each std function
the backend models arrived as one declaration per instantiation, recognized
by its mangled name.  Now each arrives as one generic declaration:

- **Recognition** is by Rust name pattern (`std_fun_table` in
  `ExtractAcl2.ml`; the mechanism of the reference backends' builtin
  tables).  `ACL2_DEBUG_PATTERNS=1` prints every declaration's pattern next
  to its mangled name.
- **Names.**  The table gives each modeled function a stable ACL2 name
  (`core-ops-range-range-next`, `core-slice-iter-itermut-next`,
  `core-array-index-range`, `u32-bitxor-assign-ref`, ...) where the mangled
  impl path would carry charon's internal clause names
  (`...-clause0-clause1-item-...`).
- **Instantiation checks.**  One model serves every instantiation, so each
  call site checks that the instantiation is one the model is valid for (a
  range of integers for `Range::next`, a `Range<usize>` under `StepBy`, a
  slice `IterMut` zipped with a slice `Iter`, a usize or range index) and
  fails loudly otherwise.  Under monomorphization that check was implicit in
  the name.
- **Fallibility** follows the AST: a call is printed monadically iff Aeneas
  typed it as a `result`.  `[T]::len`, `Vec::len` and `Vec::new` are
  infallible in Aeneas's builtin table and print as `(len v)` / `nil`.
- **Only what is used is emitted.**  Charon declares every method of every
  impl a crate touches and the types of all their signatures; a std model is
  emitted only if the crate calls it, a std type only if the emitted code
  mentions it, and an opaque std declaration nobody calls produces no line.
  A call to an unmodeled std function fails at the call site and names it.

### What changed in the generated books, against `acl2-backend`

Crate functions are the same code.  The differences are: std items are
renamed as above; `x.len()` binds without the monad; the identity
`into_iter` of a `for` loop over a range is gone (Aeneas elides it), so the
loop is called on the range directly; bound variables are numbered from 1 in
each declaration instead of across the crate, so a function's text no longer
depends on the rest of the crate or on the order charon lists it in.  In the
hand-written books this needed renames in five (63 occurrences) and the
removal of two hints that named the vanished `into_iter` wrappers.  No proof
needed rework.

### Other backend changes on this branch

- LLBC builtin function ids are gone upstream: `FunId (FRegular id)` is
  `FunId id`; single-element indexing is the pure `IndexAtIndex` /
  `IndexMutAtIndex`; `[x; N]`, `as_slice`, `as_mut_slice` are std calls
  (kinds `StdArrayRepeat`, `StdArrayAsSlice`, `StdArrayAsMutSlice`).
- **Structs are nominal throughout** (`Config.use_tuple_structs := false`
  for this backend).  With the default, the pure AST leaves it to the printer
  to erase one-field tuple structs and print the others as tuples; the
  printer emitted products but read them as conses, so construction and
  field access of a tuple struct disagreed (`no_nested_borrows` had such
  functions; nothing proved anything about them).  A struct without fields
  is `(unit)`.
- **Const generics are ordinary parameters**: a function's const generic
  parameters are its first formals, named `const-<name>` (so `N` cannot
  collide with the fuel formal `n`), and calls pass them first.
- `tests/src/generics_probe.rs` with a proofs book covers type parameters,
  const generics and tuple structs.

## Trait-generic code: one function per trait instance

A trait bound is a function-valued parameter in disguise:

    pub fn total<S: Shape, T: Shape>(s: &S, t: &T) -> u32 {
        s.area() + t.double_area()
    }

calls whatever `area` its caller picks.  In Aeneas's pure code `total` takes
the two impls as arguments and projects the methods from them
(`TraitClause(0).area s`), which a first-order ACL2 function cannot.  So the
backend specializes: a function whose code depends on a trait bound is not
printed where it is declared, but once per **instance** of the bound the
crate uses it at, with each call through the bound resolved to the function
the impl gives for the method.  `total(&Sq(2), &Rect(2, 3))` is a call to

    (defun traits-probe-total[traits-probe-sq][traits-probe-rect] (s t-var)
      (b* (((ok v1_1) (traits-probe-impl-traits-probe-shape-for-traits-probe-sq-area s)))
      (b* (((ok v2_2) (traits-probe-impl-traits-probe-shape-for-traits-probe-rect-double-area t-var)))
      (u32-add v1_1 v2_2))))

This is the part of `--monomorphize` the backend needed, done after Aeneas
instead of before it, on the pure AST (`ExtractAcl2.ml`, the section
"specialization"), with stock charon output as input:

- **Only trait instances are specialized.**  Types stay erased and const
  generics stay parameters, so one function still serves every type.  An
  instance is keyed on the function and one trait instance per bound; a
  trait instance (`dict`) is an impl applied to the instances its own bounds
  stand for (`{impl Shape for Two<S>}` at `{impl Shape for Sq}`).
- **Only the bounds the code depends on count** (`compute_relevance`, a
  least fixed point over the functions and the impls).  A bound matters to a
  function when the body calls a method or reads a constant of an instance
  built from it, or hands such an instance to a callee for a bound that
  matters there.  A function none of whose bounds matter
  (`fn first<T: Copy>(xs: &[T; 2]) -> T`) is printed once, as before: the
  generated books that existed before this change are the same byte for
  byte, except for one SKIPPED message in `demo.lisp`.
- **Names** follow the convention of the SOFT library for the instances of a
  second-order function: the function's name, then one bracket per bound
  naming the type the impl is for, the impl's own instances nested inside:
  `total[sq][rect]`, `total[two[sq]][sq]`, `mul-add[u32][u32]`,
  `apply[closures-closure]` (each with the crate prefix).  Two impls of one
  trait for types with the same head (`Shape for Wrap<u8>` and `Shape for
  Wrap<u32>`; `From<u8> for u64` and `From<u16> for u64`) both go by the
  impl's full name instead.  Which name an instance gets depends on the
  impls in the crate only, not on the order instances are met in, so a name
  never comes to mean a different instance.
- **Resolved:** required methods; provided methods (an impl's method table
  points to the trait's default, which becomes an instance at that impl);
  impls with bounds of their own, to any depth; supertraits; associated
  constants; bounds on associated types; trait methods with trait bounds of
  their own; blanket impls.
- **Closures need nothing more.**  Charon gives a closure a struct for its
  captures and impls of `Fn` / `FnMut` / `FnOnce`, so
  `apply<F: Fn(u32) -> u32>` at a closure is an instance like any other,
  calling the closure's `call`.
- **Emission.**  An instance is generated the first time a call needs it and
  written before the declaration that asked for it, the instances it needs
  itself first.  A recursive function is recursive at its instance, with the
  same measure on the fuel.  Where the generic function was declared the
  book has a comment listing its instances.  A function of the crate that is
  used at no instance has no ACL2 counterpart and is listed as SKIPPED; to
  get one, call it from a monomorphic function in the crate.
- **The std impls of the integer types, through a bound.**  In generic code
  `x + y`, `x < y`, `x == y` and `x.clone()` are calls through `Add`,
  `PartialOrd`, `PartialEq` and `Clone` bounds; at an integer type the impl
  is std's, opaque, and maps to the primitive (`std_prim_table`, 163 name
  patterns).  The same table makes derived `Clone` and `PartialEq` work for
  structs of integers in ordinary code.

`ACL2_DEBUG_TRAITS=1` prints the trait impls (clauses, method tables, parent
instances) and the bounds each function and impl depends on.

`tests/src/traits_probe.rs` exercises all of the above.  Its proofs book has
known answers (the values the compiled Rust returns) and theorems about
instances: `total` at `Sq` and `Rect` is `a*a + 2*b*c` when nothing
overflows; four closures handed to four higher-order functions come to
`29 + (5 xor k)` modulo 2^32, for every u32 `k`.

Not handled.  Each fails at the instance or at the call, with a message, and
the function is SKIPPED:

| case | why |
|---|---|
| mutually recursive trait-generic functions | instances are generated one at a time; a clique of instances would have to come out as one `mutual-recursion` |
| an impl method that reaches itself through a generic function (`impl Shape for Tree` calling `twice(&**l)`) | the instance is written before the method that asked for it |
| a modeled std function called through a bound (`for x in it` where `it: I`, `I: Iterator`) | the models check their instantiation by its type arguments, which an instance does not record |
| a method of an impl with const generic parameters, called through a bound | an instance does not record the const generic arguments of its impls either |
| an associated constant that depends on the bounds of its impl (`const ID: u32 = S::ID + 1`) | constants are not specialized |
| a closure that mutates what it captures | its `call_mut` returns a backward function (1c below) |
| a function item where a closure is expected (`apply(double, 3)`) | charon gives the item an impl of `Fn`, so the mechanism would apply, but Aeneas's `-use-fuel` pass stops on a function used as a value (internal error) |

An instance is an ordinary function, so a proof about it is an ordinary
proof; but a theorem about `total` at one instance says nothing about
another.  Stating a theorem once for all instances is what SOFT is for
(below).

Three small changes came with it: a formal the body ignores (the `()` a
closure without arguments is called with) is printed, as `acl2unused<i>`,
instead of failing the function; the type of a closure, `f::{closure}`, is
named `f-closure`, without the trailing dash of the mangled brace; and an
opaque global of another crate, like an opaque std function, gets a line in
the book only if the code refers to it.

## Toward all Rust code: what is missing, and the options

A Rust program can fall out of the pipeline in three places: Aeneas does not
translate it; the pure code Aeneas produces holds function values, which
ACL2's first-order functions cannot; or it calls a std function nobody has
modeled.  Small printer gaps are a fourth, minor, category.  The probes
referred to below are small crates run through the Lean backend (as the
reference for what Aeneas itself accepts) and the ACL2 backend.

### 1. Function values in the pure code

This is the central issue.  Aeneas's output is a typed lambda calculus, and
function values occur in it in exactly four forms:

a. **Trait dictionaries.**  A function with trait bounds takes the impls as
   arguments, and a call through a bound projects a method from one:
   `fn total<S: Shape, T: Shape>(s: &S, t: &T)` has body
   `TraitClause(0).area s ...`, and its caller passes
   `{impl Shape for Sq} {impl Shape for Rect}`.  A derived impl is a
   dictionary applied to dictionaries: `{impl Shape for Two<S>} [{impl Shape
   for Sq}]`.  The backend specializes these away (previous section).
b. **Closures.**  Charon represents a closure as a struct of its captures
   with impls of `Fn` / `FnMut` / `FnOnce`, and Aeneas translates them: the
   closure's `call` is already a first-order function.  The generic consumer
   (`fn apply<F: Fn(u32) -> u32>(f: F, x: u32)`) is case (a), so it is
   specialized too.  What remains is a closure that mutates what it
   captures: its `call_mut` returns a backward function, case (c).
c. **Backward functions.**  A function that returns a mutable borrow returns
   a pair of the value and a closure that puts a new value back:
   `choose(b, x, y) = if b then (x, fun x' -> (x', y)) else ...`.  The printer
   handles the shapes it recognizes (`iter_mut`, `zip`, mutable indexing,
   array-to-slice, and the write-back continuations of loops over them) and
   rejects the rest ("lambda in output").
d. **Function pointers and `dyn Trait`.**  Aeneas rejects these itself
   ("Function pointers are not supported yet"), so they are not yet the
   backend's problem.

Options, by what they address:

- **Specialize after Aeneas** (for a and b): done, in the printer; see the
  previous section.  In every caller reachable from non-generic code each
  dictionary argument is a closed term, an impl possibly applied to impls,
  so a generic function can be instantiated once per tuple of dictionaries,
  each method projection becoming a direct call.  The result is the
  first-order code `--monomorphize` produced, with three differences that
  matter.  Regions were consumed by Aeneas before the pass runs, so nothing
  like the erasure problem can occur.  Instances are keyed on dictionaries
  only, since the ACL2 code has no types to instantiate, so `id::<u32>` and
  `id::<u8>` stay one function.  And there is no dependency on charon beyond
  its stock output.  What is left of it is the table at the end of the
  previous section: cliques of mutually recursive instances; instances that
  record type and const generic arguments, for the modeled std functions and
  the const-generic impls reached through a bound; specialized constants.
  As a pass over the pure AST in Aeneas, rather than in this printer, it
  would serve any first-order backend.
- **Second-order functions in ACL2 (SOFT)** (for a, where a *generic*
  theorem or an uninstantiated generic function is wanted).  Kestrel's SOFT
  mimics second-order functions with function variables: a trait method
  becomes a function variable (`defunvar`), a generic function a second-order
  function (`defun2`), and an instantiation a `defun-inst`, whose result is
  first-order once no function variable is left; `defthm-inst` carries a
  theorem about the generic function to each instance by functional
  instantiation.  That is specialization performed by ACL2 itself, with
  theorem reuse, which the backend-side pass does not give.  Limits: an
  instantiation needs the instances of the functions it depends on to exist
  already (emit inner-first); mutual recursion is listed as future work; a
  generic *method* of a trait would need function variables that take
  function variables.  The instances the backend prints are already named
  the way SOFT names them (`total[sq][rect]`), so emitting `defun2` for the
  generic function and `defun-inst` for each instance, where SOFT can take
  them, would keep every name.
- **Splitting** (for the common shape of c).  When a function builds its
  backward function in tail position and the caller applies it directly,
  the function can be printed as two first-order functions, forward and
  backward, the backward one re-running the forward computation.  This is
  the scheme earlier versions of Aeneas used before it returned closures.
- **Defunctionalization** (for c in general, and d).  A closure becomes a
  tagged tuple of its captured values, and each application of an unknown
  function becomes a call to an `apply` function that dispatches on the tag.
  The loop write-back continuations are an instance of this today (a list of
  pending writes, applied by `-apply-back`).  It is closed-world, and the
  `apply` function is in a clique with whatever the closure bodies call, so
  it needs a measure; fuel serves.
- **`apply$`.**  ACL2's own first-class functions.  Function symbols become
  values with no new machinery in the printer, at the price of warrant
  hypotheses in every theorem, the restriction that a recursive function in
  a mutually recursive clique cannot be warranted, and proofs (GL in
  particular) that do not see through `apply$`.

The combination that fits the proofs done so far: specialize what is
statically known (done), split or defunctionalize what remains, and use SOFT
where a theorem should be stated once for all instantiations.

### 2. The standard library

The backend models 25 kinds of std function by table (30 patterns), each
synthesized into the book of every crate that uses it, besides the integer,
`Vec` and slice operations that map straight to the primitives book (by
mangled name, and by pattern for the integer impls of the operator,
comparison and clone traits).  That does not scale to all of std.  Three
moves, which compose:

- **A model library.**  Hand-written ACL2 books for the models, with their
  lemmas, certified once; the table maps patterns to library functions, as
  the reference backends' tables map them to their libraries.  The std types
  the models mention (`Option`, `Range`, the iterator models) then have to
  live in the library rather than in each generated book.
- **Extract std's own bodies where they are ordinary Rust.**  Much of std is
  thin generic code over trait bounds and closures (`Option::map`, the
  blanket `Into`, `==` on references, the iterator adapters).  With
  specialization its real bodies can be translated like user code: charon's
  `--include` makes a std function transparent, and the backend prints it at
  the instances the crate uses.  `tests/src/std_glue_probe.rs` does this, in
  the certified suite (the flags are `STD_GLUE` in `tests/acl2/Makefile`):

      charon rustc --preset=aeneas \
        --include core::option::_::map --include core::option::_::and_then \
        --include core::option::_::map_or --include core::option::_::unwrap_or_else \
        --include core::option::_::unwrap_or --include core::option::_::is_some \
        --include core::option::_::ok_or --include core::result::_::map \
        --include 'core::convert::{core::convert::Into<_,_>}::into' \
        --include core::convert::num::_::from --include core::cmp::impls::_::eq -- ...

  With these, `o.map(|x| x.wrapping_add(k))` is core's `Option::map` at the
  closure (`core-option-core-option-option-t-map[std-glue-probe-add-to-closure]`),
  `x.into()` goes through the blanket `Into` impl to `(u64-cast x)`, and
  `a == b` on two `&u32` reaches `(equal a b)`.  Of the book's 37 functions
  16 are core's, printed from its source, and none is a hand model; the
  proofs book states what they compute (`add_to(Some(x), k)` is
  `Some((x + k) mod 2^32)`).  It is limited by Aeneas, function by function.  Every included body has to be in its fragment: `Result::unwrap_or`
  is not ("There should be no bottoms in the value").  And an include can
  create a declaration group Aeneas rejects for the whole crate: adding
  `core::cmp::impls::_::max` (for `core::cmp::max`) gave a function mutually
  recursive with a trait impl.  The leaves stay hand models: the integer
  `Step` impls, the slice iterators (raw pointers), the intrinsics.
- **Check models against the MIR semantics.**  Each hand model is trusted.
  The interpreter can run the real std code, so a model can be tested, or
  proved, against it.

### 3. Outside Aeneas's fragment

Function pointers, `dyn`, unsafe code and raw pointers, interior mutability,
and some nestings of mutable borrows are not translated by Aeneas, and what
it accepts changes from release to release.  The executable MIR semantics
has no such fragment: it is the path for code Aeneas rejects, and the two
can be mixed function by function once a theorem relates an extracted
function to the interpreter's run of the same function.

Upstream is reported to be working on a successor ("Aeneas 2": a rewrite in
Rust, with unsafe code, raw pointers and a byte-level memory model).  If it
arrives as described, this fragment grows, and the backend -- an OCaml
printer over the pure AST -- has to be carried over.  What it does is small
and stated here so that it can be: name-pattern tables for std, per-instance
specialization of trait instances, the let shapes for backward functions.

### 4. Printer gaps, as measured on the test suite

What is still skipped across the 22 generated books (all in the three
upstream Aeneas test crates, but for the function `traits_probe` leaves
uninstantiated on purpose):

| reason | functions |
|---|---|
| backward function or closure in the output (1c) | 16 |
| tuple of arity greater than 2 | 7 |
| negation / bitwise-not | 3 |
| unmodeled std function | 2 |
| `char` / `str` / float literal | 1 |
| trait-generic, used at no instance in its crate | 2 |
| application of a function-typed variable (1c) | 1 |
| mutually recursive types | 1 group |
| calls one of the above | 11 |

### 5. Staying current with upstream

The polymorphic pipeline is the configuration upstream Aeneas runs and
tests.  Three things on this branch are there to make the next merge
cheaper: std items recognized by name pattern rather than by mangled name;
ACL2 names for them chosen here rather than derived from charon's clause
naming; and per-declaration variable numbering, so that a reordering
upstream does not rewrite every book.
