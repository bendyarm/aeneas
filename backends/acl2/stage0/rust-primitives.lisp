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

;; Bitwise, shift and wrapping ops for UNSIGNED Rust integer types.
;; - xor/and/or: total, plain value (bit width preserved).
;; - shl/shr: return result -- Rust panics if the shift amount is >= the
;;   bit width; the value shift itself is modulo 2^width (shl) or a
;;   logical right shift (shr, valid since the value is non-negative).
;; - wrapping_{add,sub,mul}: total, result-wrapped to match how Aeneas
;;   models the std methods (monadic, but never actually fail).
(defmacro def-rust-uint-bitops (name width)
  (let* ((s (symbol-name name))
         (m `(expt 2 ,width)))
    (let ((xor (intern$ (concatenate 'string s "-XOR") "ACL2"))
          (band (intern$ (concatenate 'string s "-AND") "ACL2"))
          (bor (intern$ (concatenate 'string s "-OR") "ACL2"))
          (shl (intern$ (concatenate 'string s "-SHL") "ACL2"))
          (shr (intern$ (concatenate 'string s "-SHR") "ACL2"))
          (wadd (intern$ (concatenate 'string s "-WRAPPING-ADD") "ACL2"))
          (wsub (intern$ (concatenate 'string s "-WRAPPING-SUB") "ACL2"))
          (wmul (intern$ (concatenate 'string s "-WRAPPING-MUL") "ACL2")))
      `(progn
         (defun ,xor (x y) (logxor x y))
         (defun ,band (x y) (logand x y))
         (defun ,bor (x y) (logior x y))
         (defun ,shl (x n)
           (if (< (nfix n) ,width)
               (ok (mod (ash x (nfix n)) ,m))
             (fail (err-failure))))
         (defun ,shr (x n)
           (if (< (nfix n) ,width)
               (ok (ash x (- (nfix n))))
             (fail (err-failure))))
         (defun ,wadd (x y) (ok (mod (+ x y) ,m)))
         (defun ,wsub (x y) (ok (mod (- x y) ,m)))
         (defun ,wmul (x y) (ok (mod (* x y) ,m)))))))


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

(def-rust-uint-bitops u8 8)
(def-rust-uint-bitops u16 16)
(def-rust-uint-bitops u32 32)
(def-rust-uint-bitops u64 64)
(def-rust-uint-bitops u128 128)
(def-rust-uint-bitops usize 64)

;; ---------------------------------------------------------------- arrays
;; Rust arrays [T; N] and slices &[T] are both modeled as true lists (the
;; same representation Kestrel bv-arrays use). Indexing/updating is
;; bounds-checked and returns a result; conversions between arrays and
;; slices are the identity. usize bounds are implicitly respected because
;; list lengths are.

(defun array-index (a i)
  (if (and (natp i) (< i (len a)))
      (ok (nth i a))
    (fail (err-failure))))

(defun array-update (a i v)
  (if (and (natp i) (< i (len a)))
      (ok (update-nth i v a))
    (fail (err-failure))))

(defun array-len (a) (len a))

(defun array-repeat (n x)
  (if (zp n) nil (cons x (array-repeat (1- n) x))))

;; Subslice [i..j) of a list, shared form.
(defun array-subslice (a i j)
  (if (and (natp i) (natp j) (<= i j) (<= j (len a)))
      (ok (nthcdr i (take j a)))
    (fail (err-failure))))

;; A few rules the proofs want.
(defthm array-index-ok
  (implies (and (natp i) (< i (len a)))
           (equal (array-index a i) (ok (nth i a)))))

(defthm array-index-oob
  (implies (not (and (natp i) (< i (len a))))
           (equal (array-index a i) (fail (err-failure)))))

(defthm array-update-ok
  (implies (and (natp i) (< i (len a)))
           (equal (array-update a i v) (ok (update-nth i v a)))))

(defthm len-of-array-repeat
  (equal (len (array-repeat n x)) (nfix n)))

;; ------------------------------------------------------------------ Vec
;; Rust Vec<T> is a growable array, modeled (like arrays/slices) as a list.
;; push/insert take &mut self, so Aeneas returns the updated vector; new
;; and len cannot fail. Requires the crate extracted with --monomorphize.

(defun vec-new () (ok nil))
(defun vec-len (v) (len v))
(defun vec-push (v x) (ok (append v (list x))))
(defun vec-insert (v i x)
  (if (and (natp i) (<= i (len v)))
      (ok (append (take i v) (cons x (nthcdr i v))))
    (fail (err-failure))))

(defthm len-of-vec-push
  (equal (len (result-ok->val (vec-push v x))) (+ 1 (len v))))

(defthm true-listp-of-vec-push
  (implies (true-listp v) (true-listp (result-ok->val (vec-push v x)))))

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
