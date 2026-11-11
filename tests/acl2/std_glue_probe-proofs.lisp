; Known-answer and symbolic checks for tests/src/std_glue_probe.rs: std
; functions that are generic over closures and trait bounds, extracted from
; core's own source (charon --include: STD_GLUE in the Makefile) with
; -backend acl2 -use-fuel -loops-to-rec, and printed at the trait instances
; the crate uses them at.  There is no hand-written model behind any function
; in this book: Option::map is core's Option::map.
(in-package "ACL2")
(include-book "std_glue_probe")
(local (include-book "arithmetic-5/top" :dir :system))

;; ---- Option::map, at the closure |x| x.wrapping_add(k) ----
(defthm add-to-some
  (equal (std-glue-probe-add-to (core-option-option-some x) k)
         (ok (core-option-option-some (mod (+ x k) 4294967296)))))

(defthm add-to-none
  (equal (std-glue-probe-add-to (core-option-option-none) k)
         (ok (core-option-option-none))))

;; ---- Option::and_then, at a closure that returns an Option ----
(defthm half-known-answers
  (and (equal (std-glue-probe-half (core-option-option-some 10))
              (ok (core-option-option-some 5)))
       (equal (std-glue-probe-half (core-option-option-some 7))
              (ok (core-option-option-none)))
       (equal (std-glue-probe-half (core-option-option-none))
              (ok (core-option-option-none)))))

;; ---- Option::map_or ----
(defthm or-k-some
  (equal (std-glue-probe-or-k (core-option-option-some x) k)
         (ok (mod (* 2 x) 4294967296))))

(defthm or-k-none
  (equal (std-glue-probe-or-k (core-option-option-none) k)
         (ok k)))

;; ---- Option::unwrap_or_else, at a closure without arguments ----
(defthm or-else-some
  (equal (std-glue-probe-or-else (core-option-option-some x) k)
         (ok x)))

(defthm or-else-none
  (equal (std-glue-probe-or-else (core-option-option-none) k)
         (ok (mod (+ 1 k) 4294967296))))

;; ---- Result::map ----
(defthm res-map-ok
  (equal (std-glue-probe-res-map (core-result-result-ok x) k)
         (ok (core-result-result-ok (logxor x k)))))

(defthm res-map-err
  (equal (std-glue-probe-res-map (core-result-result-err e) k)
         (ok (core-result-result-err e))))

;; ---- no closure: unwrap_or, is_some, ok_or ----
(defthm or-zero-cases
  (and (equal (std-glue-probe-or-zero (core-option-option-some x)) (ok x))
       (equal (std-glue-probe-or-zero (core-option-option-none)) (ok 0))))

(defthm has-cases
  (and (equal (std-glue-probe-has (core-option-option-some x)) (ok t))
       (equal (std-glue-probe-has (core-option-option-none)) (ok nil))))

(defthm need-cases
  (and (equal (std-glue-probe-need (core-option-option-some x))
              (ok (core-result-result-ok x)))
       (equal (std-glue-probe-need (core-option-option-none))
              (ok (core-result-result-err 7)))))

;; ---- x.into(): the blanket Into over From, three instances ----
(defthm widen-sum-is-the-sum
  (implies (and (u8p a) (u16p b) (u32p c))
           (equal (std-glue-probe-widen-sum a b c)
                  (ok (+ a b c)))))

;; ---- == on references ----
(defthm same-u32-is-equal
  (equal (std-glue-probe-same-u32 a b)
         (ok (equal a b))))

;; ---- the composition ----
(defthm driver-known-answer
  (equal (std-glue-probe-driver) (ok 2092)))
