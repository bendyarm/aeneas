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
