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

## Known workaround: the `fail` runtime macro collides with centaur/gl

The Phase-2 bijection proof (`tests/acl2/aes_fixslice_bijection.lisp`) bit-blasts
the extracted `bitslice`/`inv_bitslice` with **centaur/gl**, so a single ACL2
world must hold both the extracted code and GL. It cannot: `rust-primitives`
defines `fail` as a *macro* (a one-line alias, `(defmacro fail (e) `(result-fail
,e))`), while centaur/gl transitively defines a *function* named `fail`
(`misc/hons-help`). ACL2 forbids a macro and a function to share a name in one
world, so `(include-book "centaur/gl/gl")` after the extracted book aborts with
"The name FAIL is in use as a macro." (`ok`, `array-index`, `u32p`, … do NOT
collide — `fail` is the only one.)

Two fixes:

1. **GL-compatible variant (used now).** The Makefile `gl-variants` target
   `sed`-rewrites `(fail …)` to its expansion `(result-fail …)` and drops the
   macro definition, producing `rust-primitives-gl.lisp` and
   `aes_fixslice_encrypt-gl.lisp`. The rewrite is purely mechanical and
   semantics-preserving (every function *body* is identical), so a theorem about
   the `-gl` functions is a theorem about the real extracted code. The variants
   are build artifacts, never hand-edited, and regenerate whenever the canonical
   books change. Self-contained; touches nothing else.

2. **Principled fix (TODO in the runtime/printer).** Give the runtime's monad
   sugar a collision-proof name — either emit `result-fail`/`result-ok` directly
   (drop the macros) or rename to something namespaced (e.g. `rust-fail`), so
   *every* extracted book is GL-ready without a variant copy. Deferred because it
   touches the printer, all generated books, and the handwritten proofs that
   mention `fail`; parallel to the unrolling workaround above (do the mechanical
   thing now, land the invasive rename deliberately). Not urgent.
