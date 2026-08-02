; Stage 0: hand-transliteration of a representative slice of the Aeneas
; output for tests/src/no_nested_borrows.rs (source of truth:
; tests/lean/NoNestedBorrows.lean).  New ground covered relative to demo.lisp:
;   - struct (Pair) -> fty::defprod, with erased type parameters
;   - multi-variant enums with payloads (Sum) and without (Enum)
;   - tuples in return types -> plain conses (Stage-0 decision)
;   - massert / extracted unit tests
;   - `choose`, a function RETURNING a backward function (from returning
;     &mut) -- translated by DEFUNCTIONALIZATION: the two lambdas become a
;     closure tagsum + a first-order apply dispatcher.  This is the
;     pressure test for plan section 3.5's primary recommendation.
;
; Naming note: the Rust type is `List`; we prefix everything `nnb-`
; (simulating crate qualification) which also dodges collisions with
; built-in LIST -- difficulty #6 of the plan showing up on schedule.

(in-package "ACL2")

(include-book "rust-primitives")

;; ---------------------------------------------------------------------
;; struct Pair<T1, T2> { x: T1, y: T2 }         (type params erased)
;; ---------------------------------------------------------------------

;; Backend lesson: FTY's default "whole-product variable" is X, which
;; collides with Rust fields named x.  Generated defprods must always
;; emit an explicit :xvar with a reserved name.
(fty::defprod nnb-pair
  ((x any-p)
   (y any-p))
  :xvar the-nnb-pair)

;; enum List<T> { Cons(T, Box<List<T>>), Nil }

(fty::deftagsum nnb-list
  (:cons ((hd any-p) (tl nnb-list-p)))
  (:nil ()))

;; enum Enum { Variant1, Variant2 }

(fty::deftagsum nnb-enum
  (:variant1 ())
  (:variant2 ()))

;; enum Sum<T1, T2> { Left(T1), Right(T2) }

(fty::deftagsum nnb-sum
  (:left ((v any-p)))
  (:right ((v any-p))))

;; ---------------------------------------------------------------------
;; fn get_max(x: u32, y: u32) -> u32
;; Lean: if x >= y then ok x else ok y      (comparison is pure)
;; ---------------------------------------------------------------------

(defun nnb-get-max (x y)
  (if (>= x y) (ok x) (ok y)))

;; fn is_cons<T>(l: &List<T>) -> bool

(defun nnb-is-cons (l)
  (nnb-list-case l
    :cons (ok t)
    :nil (ok nil)))

;; fn split_list<T>(l: List<T>) -> (T, List<T>)
;; Tuple result -> cons.

(defun nnb-split-list (l)
  (nnb-list-case l
    :cons (ok (cons (nnb-list-cons->hd l) (nnb-list-cons->tl l)))
    :nil (fail (err-failure))))

;; ---------------------------------------------------------------------
;; fn choose<'a, T>(b: bool, x: &'a mut T, y: &'a mut T) -> &'a mut T
;;
;; Aeneas pure output (higher-order -- returns a backward function):
;;   def choose (b : Bool) (x y : T) : Result (T × (T → (T × T))) := do
;;     if b then let back := fun x1 => (x1, y); ok (x, back)
;;          else let back := fun y1 => (x, y1); ok (y, back)
;;
;; Defunctionalized: the closure environment becomes data, application
;; becomes a first-order dispatcher.  At extraction time the set of
;; lambdas is closed, so this is fully mechanical.
;; ---------------------------------------------------------------------

(fty::deftagsum nnb-choose-back
  (:on-true ((y any-p)))    ; back := fun x1 => (x1, y)   captures y
  (:on-false ((x any-p)))   ; back := fun y1 => (x, y1)   captures x
  :xvar the-clos)           ; same :xvar lesson as nnb-pair above

(defun nnb-apply-choose-back (clos ret)
  (nnb-choose-back-case clos
    :on-true (cons ret (nnb-choose-back-on-true->y clos))
    :on-false (cons (nnb-choose-back-on-false->x clos) ret)))

(defun nnb-choose (b x y)
  (if b
      (ok (cons x (nnb-choose-back-on-true y)))
    (ok (cons y (nnb-choose-back-on-false x)))))

;; fn choose_test()  -- the caller: writes z+1 through the returned &mut.
;; Lean:
;;   let (z, choose_back) ← choose true 0 0
;;   let z1 ← z + 1
;;   massert (z1 = 1)
;;   let (x, y) := choose_back z1
;;   massert (x = 1); massert (y = 0)

(defun nnb-choose-test ()
  (b* (((ok zc) (nnb-choose t 0 0))
       (z (car zc))
       (back (cdr zc))
       ((ok z1) (i32-add z 1))
       ((ok &) (massert (equal z1 1)))
       (xy (nnb-apply-choose-back back z1))
       ((ok &) (massert (equal (car xy) 1))))
    (massert (equal (cdr xy) 0))))

;; ---------------------------------------------------------------------
;; Concrete-execution unit tests, mirroring the generated `#assert`s.
;; ---------------------------------------------------------------------

(assert-event (equal (nnb-get-max 3 7) (ok 7)))
(assert-event (equal (nnb-is-cons (nnb-list-cons 0 (nnb-list-nil))) (ok t)))
(assert-event (equal (nnb-split-list (nnb-list-cons 0 (nnb-list-nil)))
                     (ok (cons 0 (nnb-list-nil)))))
(assert-event (equal (nnb-split-list (nnb-list-nil)) (fail (err-failure))))
(assert-event (equal (nnb-choose-test) (ok (unit))))   ; #assert choose_test == ok ()
