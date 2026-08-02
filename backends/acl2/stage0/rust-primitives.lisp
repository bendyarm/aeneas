; Stage 0 prototype of the Aeneas ACL2 primitives book.
; Mirrors backends/coq/Primitives.v: error = Failure | OutOfFuel;
; result a = Ok a | Fail error.  FTY style per design decision.
; Scope: only what the hand-translated demo/loops examples need.

(in-package "ACL2")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/bstar" :dir :system)

;; ---------------------------------------------------------------- errors

(fty::deftagsum rust-error
  (:failure ())
  (:out-of-fuel ()))

(defmacro err-failure () '(rust-error-failure))
(defmacro err-out-of-fuel () '(rust-error-out-of-fuel))

;; ---------------------------------------------------------------- result
;; Untyped payload (any-p): one result type serves every Rust type.

(fty::deftagsum result
  (:ok ((val any-p)))
  (:fail ((err rust-error-p))))

(defmacro ok (x) `(result-ok ,x))
(defmacro fail (e) `(result-fail ,e))

;; Monadic bind as a b* binder:  (b* (((ok x) (u32-add a b))) ...)
;; short-circuits on :fail, binding the payload otherwise.

(def-b*-binder ok
  :decls ((declare (xargs :guard t)))
  :body
  `(b* ((patbind-ok-tmp-do-not-use ,(car forms)))
     (if (eq (result-kind patbind-ok-tmp-do-not-use) :ok)
         (b* ((,(car args) (result-ok->val patbind-ok-tmp-do-not-use)))
           ,rest-expr)
       patbind-ok-tmp-do-not-use)))

;; ---------------------------------------------------------------- integers
;; Checked machine-integer ops.  Uniform pattern: compute in Z, return
;; (ok r) iff r is in range, else (fail (err-failure)) -- matching
;; Aeneas's panic-on-overflow semantics.  Division/remainder use
;; truncate/rem (Rust rounds toward zero), never floor/mod.

(defconst *u32-max* (1- (expt 2 32)))
(defconst *i32-min* (- (expt 2 31)))
(defconst *i32-max* (1- (expt 2 31)))

(defun u32p (x)
  (declare (xargs :guard t))
  (and (natp x) (<= x *u32-max*)))

(defun i32p (x)
  (declare (xargs :guard t))
  (and (integerp x) (<= *i32-min* x) (<= x *i32-max*)))

(defun u32-add (x y)
  (let ((r (+ x y))) (if (u32p r) (ok r) (fail (err-failure)))))

(defun u32-sub (x y)
  (let ((r (- x y))) (if (u32p r) (ok r) (fail (err-failure)))))

(defun u32-mul (x y)
  (let ((r (* x y))) (if (u32p r) (ok r) (fail (err-failure)))))

(defun u32-div (x y)
  (if (eql y 0)
      (fail (err-failure))
    (let ((r (truncate x y))) (if (u32p r) (ok r) (fail (err-failure))))))

(defun u32-rem (x y)
  (if (eql y 0)
      (fail (err-failure))
    (let ((r (rem x y))) (if (u32p r) (ok r) (fail (err-failure))))))

(defun i32-add (x y)
  (let ((r (+ x y))) (if (i32p r) (ok r) (fail (err-failure)))))

(defun i32-sub (x y)
  (let ((r (- x y))) (if (i32p r) (ok r) (fail (err-failure)))))

;; i32::MIN / -1 overflows: captured uniformly by the range check on r.
(defun i32-div (x y)
  (if (eql y 0)
      (fail (err-failure))
    (let ((r (truncate x y))) (if (i32p r) (ok r) (fail (err-failure))))))

;; ---------------------------------------------------------------- misc
;; Rust unit value, and Aeneas's massert (used by extracted unit tests).

(defmacro unit () :unit)

(defun massert (b)
  (if b (ok (unit)) (fail (err-failure))))

;; ------------------------------------------------- characterization rules
;; The seed of the Stage-1 rule library: rewrite checked ops to ok/fail
;; under arithmetic side conditions, so proofs about extracted code never
;; open the op definitions.

(defthm u32-add-ok
  (implies (and (u32p x) (u32p y) (<= (+ x y) *u32-max*))
           (equal (u32-add x y) (ok (+ x y)))))

(defthm u32-add-overflow
  (implies (and (u32p x) (u32p y) (> (+ x y) *u32-max*))
           (equal (u32-add x y) (fail (err-failure)))))

(defthm u32-sub-ok
  (implies (and (u32p x) (u32p y) (<= y x))
           (equal (u32-sub x y) (ok (- x y)))))

(defthm u32-sub-underflow
  (implies (and (u32p x) (u32p y) (< x y))
           (equal (u32-sub x y) (fail (err-failure)))))

(defthm u32-mul-ok
  (implies (and (u32p x) (u32p y) (<= (* x y) *u32-max*))
           (equal (u32-mul x y) (ok (* x y)))))

(defthm i32-add-ok
  (implies (and (i32p x) (i32p y) (<= *i32-min* (+ x y)) (<= (+ x y) *i32-max*))
           (equal (i32-add x y) (ok (+ x y)))))

(defthm i32-sub-ok
  (implies (and (i32p x) (i32p y) (<= *i32-min* (- x y)) (<= (- x y) *i32-max*))
           (equal (i32-sub x y) (ok (- x y)))))

;; Sanity checks (concrete execution, incl. panic edges).
(assert-event (equal (u32-add 1 2) (ok 3)))
(assert-event (equal (u32-add *u32-max* 1) (fail (err-failure))))
(assert-event (equal (u32-sub 0 1) (fail (err-failure))))
(assert-event (equal (u32-div 7 2) (ok 3)))
(assert-event (equal (u32-rem 7 2) (ok 1)))
(assert-event (equal (u32-div 7 0) (fail (err-failure))))
(assert-event (equal (i32-div -7 2) (ok -3)))     ; truncation toward zero
(assert-event (equal (i32-div *i32-min* -1) (fail (err-failure)))) ; MIN / -1
