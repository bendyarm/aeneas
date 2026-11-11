; Known-answer and symbolic checks for tests/src/generics_probe.rs: generic
; code extracted from polymorphic LLBC (stock charon, --preset=aeneas) with
; -backend acl2 -use-fuel -loops-to-rec, and no monomorphization.
;
; Type parameters leave no trace in the ACL2 functions.  Const generics are
; ordinary parameters, the first formals (const-n).  Tuple structs are FTY
; products with fields f0, f1, ...; a struct without fields is (unit).
(in-package "ACL2")
(include-book "generics_probe")

;; ---- type parameters: one function serves every instantiation ----
(defthm id-is-the-identity
  (equal (generics-probe-id x) (ok x)))

(defthm swap-swaps
  (equal (generics-probe-swap (generics-probe-pair x y))
         (ok (generics-probe-pair y x))))

;; ---- const generics ----
;; one function, two array lengths
(defthm sum-arr-known-answers
  (and (equal (generics-probe-sum-arr 3 100 (list 1 2 3)) (ok 6))
       (equal (generics-probe-sum-arr 5 100 (list 1 2 3 4 5)) (ok 15))))

;; N is a parameter like any other: claim one element too many and the
;; bounds check fails, as the indexing panic would in Rust.
(defthm sum-arr-beyond-the-array
  (equal (generics-probe-sum-arr 4 100 (list 1 2 3))
         (result-fail (err-failure))))

;; [0u32; N], for every N
(defthm zeros-has-length-n
  (implies (natp n)
           (equal (len (result-ok->val (generics-probe-zeros n))) n)))

;; a const generic handed on to two callees
(defthm sum-zeros-known-answer
  (equal (generics-probe-sum-zeros 5 100) (ok 0)))

;; ---- tuple structs ----
(defthm area-of-rect
  (equal (generics-probe-generics-probe-rect-area (generics-probe-rect 6 3))
         (ok 18)))

;; `Rect(r.0 + by.0, r.1)`: constructing, reading and updating a tuple struct
;; agree with each other.
(defthm widen-changes-the-first-field-only
  (implies (and (u32p w) (u32p d) (u32p (+ w d)))
           (equal (generics-probe-widen (generics-probe-rect w h)
                                        (generics-probe-meters d)
                                        (unit))
                  (ok (generics-probe-rect (+ w d) h)))))

;; ---- the composition: 18 + 6 + 0 + 1 ----
(defthm driver-known-answer
  (equal (generics-probe-driver 100) (ok 25)))
