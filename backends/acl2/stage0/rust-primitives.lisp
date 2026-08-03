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

;; ---------------------------------------------------- all integer types
;; Macro-generated recognizers and checked ops for the remaining Rust
;; integer types (u32/i32 above are hand-written and used by the earliest
;; proofs). usize/isize are modeled as 64-bit here; upstream Aeneas
;; currently pins usize to 32 bits in the F* primitives with a TODO --
;; revisit for consistency once upstream decides (plan section 5.4).

(defmacro def-rust-int-type (name min max)
  (let* ((s (symbol-name name)))
    (let ((pred (intern$ (concatenate 'string s "P") "ACL2"))
          (add (intern$ (concatenate 'string s "-ADD") "ACL2"))
          (sub (intern$ (concatenate 'string s "-SUB") "ACL2"))
          (mul (intern$ (concatenate 'string s "-MUL") "ACL2"))
          (dv (intern$ (concatenate 'string s "-DIV") "ACL2"))
          (rm (intern$ (concatenate 'string s "-REM") "ACL2"))
          (add-ok (intern$ (concatenate 'string s "-ADD-OK") "ACL2"))
          (add-fail (intern$ (concatenate 'string s "-ADD-FAIL") "ACL2"))
          (sub-ok (intern$ (concatenate 'string s "-SUB-OK") "ACL2"))
          (sub-fail (intern$ (concatenate 'string s "-SUB-FAIL") "ACL2"))
          (mul-ok (intern$ (concatenate 'string s "-MUL-OK") "ACL2")))
      `(progn
         (defun ,pred (x)
           (declare (xargs :guard t))
           (and (integerp x) (<= ,min x) (<= x ,max)))
         (defun ,add (x y)
           (let ((r (+ x y))) (if (,pred r) (ok r) (fail (err-failure)))))
         (defun ,sub (x y)
           (let ((r (- x y))) (if (,pred r) (ok r) (fail (err-failure)))))
         (defun ,mul (x y)
           (let ((r (* x y))) (if (,pred r) (ok r) (fail (err-failure)))))
         (defun ,dv (x y)
           (if (eql y 0) (fail (err-failure))
             (let ((r (truncate x y)))
               (if (,pred r) (ok r) (fail (err-failure))))))
         (defun ,rm (x y)
           (if (eql y 0) (fail (err-failure))
             (let ((r (rem x y)))
               (if (,pred r) (ok r) (fail (err-failure))))))
         (defthm ,add-ok
           (implies (and (,pred x) (,pred y) (,pred (+ x y)))
                    (equal (,add x y) (ok (+ x y)))))
         (defthm ,add-fail
           (implies (and (,pred x) (,pred y) (not (,pred (+ x y))))
                    (equal (,add x y) (fail (err-failure)))))
         (defthm ,sub-ok
           (implies (and (,pred x) (,pred y) (,pred (- x y)))
                    (equal (,sub x y) (ok (- x y)))))
         (defthm ,sub-fail
           (implies (and (,pred x) (,pred y) (not (,pred (- x y))))
                    (equal (,sub x y) (fail (err-failure)))))
         (defthm ,mul-ok
           (implies (and (,pred x) (,pred y) (,pred (* x y)))
                    (equal (,mul x y) (ok (* x y)))))))))

(def-rust-int-type u8 0 255)
(def-rust-int-type u16 0 65535)
(def-rust-int-type u64 0 18446744073709551615)
(def-rust-int-type u128 0 340282366920938463463374607431768211455)
(def-rust-int-type usize 0 18446744073709551615)
(def-rust-int-type i8 -128 127)
(def-rust-int-type i16 -32768 32767)
(def-rust-int-type i64 -9223372036854775808 9223372036854775807)
(def-rust-int-type i128 -170141183460469231731687303715884105728
                        170141183460469231731687303715884105727)
(def-rust-int-type isize -9223372036854775808 9223372036854775807)

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
