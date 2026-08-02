; Stage 0: handwritten ACL2 specs and equivalence proofs for the
; hand-transliterated Aeneas output in demo.lisp.  This is the ACL2
; analog of tests/lean/Demo/Properties.lean, and the template for the
; per-crate `properties.lisp` books the test suite will carry.

(in-package "ACL2")

(include-book "demo")
(include-book "arithmetic/top-with-meta" :dir :system)

;; ---------------------------------------------------------------------
;; demo::mul2_add1 -- total characterization: ok case and overflow case.
;; ---------------------------------------------------------------------

(defthm demo-mul2-add1-ok
  (implies (and (u32p x)
                (<= (+ (* 2 x) 1) *u32-max*))
           (equal (demo-mul2-add1 x)
                  (ok (+ (* 2 x) 1)))))

(defthm demo-mul2-add1-overflow
  (implies (and (u32p x)
                (> (+ (* 2 x) 1) *u32-max*))
           (equal (demo-mul2-add1 x)
                  (fail (err-failure)))))

(defthm demo-use-mul2-add1-ok
  (implies (and (u32p x) (u32p y)
                (<= (+ (* 2 x) 1 y) *u32-max*))
           (equal (demo-use-mul2-add1 x y)
                  (ok (+ (* 2 x) 1 y)))))

;; ---------------------------------------------------------------------
;; demo::list_nth == nth over the meaning function clist->list.
;; ---------------------------------------------------------------------

(defun clist->list (l)
  (declare (xargs :measure (clist-count l)))
  (clist-case l
    :ccons (cons (clist-ccons->hd l) (clist->list (clist-ccons->tl l)))
    :cnil nil))

;; Opener rules for the meaning function (recursive definitions do not
;; open by themselves under an unrelated induction).
(defthm clist->list-when-ccons
  (implies (equal (clist-kind l) :ccons)
           (equal (clist->list l)
                  (cons (clist-ccons->hd l)
                        (clist->list (clist-ccons->tl l)))))
  :hints (("Goal" :expand ((clist->list l)))))

(defthm clist->list-when-not-ccons
  (implies (not (equal (clist-kind l) :ccons))
           (equal (clist->list l) nil))
  :hints (("Goal" :expand ((clist->list l)))))

(defthm demo-list-nth-correct
  (implies (and (u32p i)
                (< i (len (clist->list l)))
                (< (len (clist->list l)) (nfix fuel)))
           (equal (demo-list-nth fuel l i)
                  (ok (nth i (clist->list l)))))
  :hints (("Goal" :induct (demo-list-nth fuel l i))))

;; Fuel irrelevance, proved via a two-fuel induction scheme.  Stage 3
;; turns this pattern into a macro (def-fuel-irrelevance).

(defun demo-list-nth-ind2 (f1 f2 l i)
  (declare (xargs :measure (nfix f1)))
  (cond ((zp f1) (list f2 l i))
        ((zp f2) nil)
        ((and (eq (clist-kind l) :ccons) (not (eql i 0)) (u32p i))
         (demo-list-nth-ind2 (1- f1) (1- f2) (clist-ccons->tl l) (1- i)))
        (t nil)))

(defthm demo-list-nth-fuel-irrelevance
  (implies (and (u32p i)
                (<= (nfix f1) (nfix f2))
                (not (equal (demo-list-nth f1 l i)
                            (fail (err-out-of-fuel)))))
           (equal (demo-list-nth f2 l i)
                  (demo-list-nth f1 l i)))
  :hints (("Goal" :induct (demo-list-nth-ind2 f1 f2 l i))))

;; ---------------------------------------------------------------------
;; demo::i32_id is the identity on non-negative i32s.
;; ---------------------------------------------------------------------

(defthm demo-i32-id-correct
  (implies (and (i32p n)
                (<= 0 n)
                (< n (nfix fuel)))
           (equal (demo-i32-id fuel n) (ok n)))
  :hints (("Goal" :induct (demo-i32-id fuel n))))

;; ---------------------------------------------------------------------
;; loops::sum == closed-form spec.
;; sum-spec i max = i + (i+1) + ... + (max-1), the natural recursive spec;
;; the Gauss closed form is then a lemma about sum-spec alone, i.e. pure
;; arithmetic separated from the extraction artifact.
;; ---------------------------------------------------------------------

(defun sum-spec (i max)
  (declare (xargs :measure (nfix (- max i))))
  (if (and (natp i) (natp max) (< i max))
      (+ i (sum-spec (+ 1 i) max))
    0))

(defthm natp-sum-spec
  (natp (sum-spec i max))
  :rule-classes :type-prescription)

(defthm sum-spec-lower-bound
  (implies (and (natp i) (natp max) (< i max))
           (<= i (sum-spec i max)))
  :rule-classes :linear)

;; Loop invariant lemma: running the loop from state (i, s) adds the
;; remaining partial sum to the accumulator.
(defthm loops-sum-loop-correct
  (implies (and (u32p max) (u32p i) (u32p s)
                (<= i max)
                (< (- max i) (nfix fuel))
                (<= (+ s (sum-spec i max)) *u32-max*))
           (equal (loops-sum-loop fuel max i s)
                  (ok (+ s (sum-spec i max)))))
  :hints (("Goal" :induct (loops-sum-loop fuel max i s))))

(defthm loops-sum-correct
  (implies (and (u32p max)
                (< max (nfix fuel))
                (<= (sum-spec 0 max) *u32-max*))
           (equal (loops-sum fuel max)
                  (ok (sum-spec 0 max)))))

;; The pure-arithmetic half: Gauss.  (sum-spec 0 max) = max*(max-1)/2.
(defthm sum-spec-closed-form
  (implies (and (natp i) (natp max))
           (equal (sum-spec i max)
                  (if (< i max)
                      (/ (- (* max (- max 1)) (* i (- i 1))) 2)
                    0)))
  :hints (("Goal" :induct (sum-spec i max)))
  :rule-classes nil)
