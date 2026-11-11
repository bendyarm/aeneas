; Known-answer and symbolic checks for tests/src/traits_probe.rs: trait-generic
; code, extracted from polymorphic LLBC (stock charon, --preset=aeneas) with
; -backend acl2 -use-fuel -loops-to-rec.
;
; A function that calls through one of its trait bounds is printed once per
; instance of the bound the crate uses it at.  The name is the function's
; followed by one bracket per bound, each naming the type the impl is for:
; total<S: Shape, T: Shape> at Sq and Rect is
; traits-probe-total[traits-probe-sq][traits-probe-rect].  In an instance the
; calls through the bounds are calls to the functions of the impls, so it is an
; ordinary first-order function, and a proof about it is an ordinary proof.
(in-package "ACL2")
(include-book "traits_probe")
(local (include-book "arithmetic-5/top" :dir :system))

;; ---- an instance calls the functions of its impls ----

;; total(s, t) = s.area() + t.double_area().  At Sq and Rect that is Sq's
;; area and the double_area Rect overrides, 2 * w * h.
(defthm total-at-sq-and-rect
  (implies (and (u32p a) (u32p b) (u32p c)
                (u32p (* a a)) (u32p (* 2 b)) (u32p (* 2 b c))
                (u32p (+ (* a a) (* 2 b c))))
           (equal (traits-probe-total[traits-probe-sq][traits-probe-rect]
                   (traits-probe-sq a) (traits-probe-rect b c))
                  (ok (+ (* a a) (* 2 b c))))))

;; Sq does not override double_area: its instance is the trait's provided
;; method, area() * 2, at Sq.
(defthm double-area-at-sq
  (implies (and (u32p a) (u32p (* a a)) (u32p (* 2 a a)))
           (equal (traits-probe-shape-double-area[traits-probe-sq]
                   (traits-probe-sq a))
                  (ok (* 2 a a)))))

;; The impl for Two<S> has a bound of its own, so its methods have instances
;; too, and an instance can be at an instance: Two<Two<Sq>>.
(defthm area-of-two-at-sq
  (implies (and (u32p a) (u32p b) (u32p (* a a)) (u32p (* b b))
                (u32p (+ (* a a) (* b b))))
           (equal (traits-probe-impl-traits-probe-shape-for-traits-probe-two-s-area[traits-probe-sq]
                   (traits-probe-two (traits-probe-sq a) (traits-probe-sq b)))
                  (ok (+ (* a a) (* b b))))))

(defthm shapes-known-answer
  (equal (traits-probe-shapes) (ok 80)))

;; ---- loops and recursion at an instance ----
(defthm sum-areas-known-answers
  (and (equal (traits-probe-sum-areas[traits-probe-sq]
               100 (list (traits-probe-sq 1) (traits-probe-sq 2) (traits-probe-sq 3)))
              (ok 14))
       (equal (traits-probe-sum-areas[traits-probe-rect]
               100 (list (traits-probe-rect 1 2) (traits-probe-rect 3 4)))
              (ok 14))))

;; the area overflows u32: the instance fails where the Rust panics
(defthm sum-areas-overflow
  (equal (traits-probe-sum-areas[traits-probe-sq]
          100 (list (traits-probe-sq 65536)))
         (result-fail (err-failure))))

(defthm pow-area-known-answer
  (equal (traits-probe-pow-area[traits-probe-rect] 100 (traits-probe-rect 1 2) 3)
         (ok 8)))

;; a const generic stays a parameter of the instance
(defthm sum-all-known-answer
  (equal (traits-probe-sum-all[traits-probe-sq]
          2 100 (list (traits-probe-sq 1) (traits-probe-sq 2)))
         (ok 5)))

(defthm loops-known-answer
  (equal (traits-probe-loops 100) (ok 41)))

;; ---- supertraits, associated constants and types, blanket impls ----

;; via_super(n) = n.area() + n.id_plus_area(), where area comes from the
;; supertrait instance and id_plus_area reads the associated constant (7).
(defthm via-super-at-sq
  (implies (and (u32p a) (u32p (* a a)) (u32p (+ 7 (* 2 a a))))
           (equal (traits-probe-via-super[traits-probe-sq] (traits-probe-sq a))
                  (ok (+ 7 (* 2 a a))))))

;; the blanket impl of Describe, for a T that is Sq
(defthm describe-it-at-sq
  (implies (and (u32p a) (u32p (* a a)) (u32p (+ 100 (* a a))))
           (equal (traits-probe-describe-it[traits-probe-sq] (traits-probe-sq a))
                  (ok (+ 100 (* a a))))))

(defthm traits-known-answer
  (equal (traits-probe-traits) (ok 149)))

;; ---- closures ----

;; apply(f, x) = f(x).  A closure is a struct of what it captures, here k, and
;; `apply` at the closure |x| x.wrapping_add(k) is that addition.
(defthm apply-at-the-first-closure
  (equal (traits-probe-apply[traits-probe-closures-closure]
          (traits-probe-closures-closure k) x)
         (u32-wrapping-add x k)))

;; the closure kept in a struct
(defthm mapper-run-at-the-fourth-closure
  (equal (traits-probe-traits-probe-mapper-f-run[traits-probe-closures-closure-3]
          (traits-probe-mapper (traits-probe-closures-closure-3 k)) x)
         (ok (u32-xor x k))))

;; Four closures, handed to four higher-order functions:
;; (1 + k) + 18 + (10 - k) + (5 ^ k), wrapping.
(defthm closures-is-29-plus-5-xor-k
  (implies (u32p k)
           (equal (traits-probe-closures k)
                  (ok (mod (+ 29 (logxor 5 k)) 4294967296)))))

(defthm closures-known-answers
  (and (equal (traits-probe-closures 0) (ok 34))
       (equal (traits-probe-closures 5) (ok 29))
       (equal (traits-probe-closures 12345678) (ok 12345704))
       (equal (traits-probe-closures 4294967295) (ok 23))))

;; ---- the std impls of the integer types, through a bound ----
(defthm mul-add-at-u32
  (implies (and (u32p a) (u32p b) (u32p (* a b)) (u32p (+ a (* a b))))
           (equal (traits-probe-mul-add[u32][u32] a b)
                  (ok (+ a (* a b))))))

(defthm max-gen-at-u32
  (equal (traits-probe-max-gen[u32] a b)
         (ok (if (> a b) a b))))

(defthm same-at-u8
  (equal (traits-probe-same[u8] a b)
         (ok (equal a b))))

(defthm dup-at-u32
  (equal (traits-probe-dup[u32] a)
         (ok (cons a a))))

(defthm std-impls-known-answer
  (equal (traits-probe-std-impls) (ok 51)))

;; ---- a bound no code calls through: one function for every type ----
(defthm first-is-the-first
  (equal (traits-probe-first (list x y)) (ok x)))

;; ---- the composition: 80 + 41 + 149 + 51 ----
(defthm driver-known-answer
  (equal (traits-probe-driver 100) (ok 321)))
