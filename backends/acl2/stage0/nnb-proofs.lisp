; Stage 0: specs and equivalence proofs for nnb.lisp -- most importantly
; the ROUNDTRIP theorem for the defunctionalized `choose`, which is the
; feasibility evidence for handling Aeneas backward functions first-order
; (plan section 3.5, primary recommendation).

(in-package "ACL2")

(include-book "nnb")
(include-book "arithmetic/top-with-meta" :dir :system)

;; ---------------------------------------------------------------------
;; get_max == max
;; ---------------------------------------------------------------------

(defthm nnb-get-max-correct
  (implies (and (u32p x) (u32p y))
           (equal (nnb-get-max x y) (ok (max x y)))))

;; ---------------------------------------------------------------------
;; split_list: total characterization.
;; ---------------------------------------------------------------------

(defthm nnb-split-list-when-cons
  (implies (equal (nnb-list-kind l) :cons)
           (equal (nnb-split-list l)
                  (ok (cons (nnb-list-cons->hd l) (nnb-list-cons->tl l))))))

(defthm nnb-split-list-when-nil
  (implies (not (equal (nnb-list-kind l) :cons))
           (equal (nnb-split-list l) (fail (err-failure)))))

;; ---------------------------------------------------------------------
;; The defunctionalization pressure test.
;;
;; Rust semantics of the caller pattern
;;     let z = choose(b, &mut x, &mut y);  *z += 1;
;; is: if b then (x+1, y) else (x, y+1).
;;
;; The theorem states that the extracted pipeline -- call `choose`, add 1
;; to the returned value, then apply the (defunctionalized) backward
;; function -- computes exactly that, for ALL inputs in range.  The
;; concrete `choose_test` assert in nnb.lisp is the i32/0/0 instance.
;; ---------------------------------------------------------------------

(defthm nnb-choose-back-roundtrip
  (implies (and (i32p x) (i32p y)
                (< x *i32-max*) (< y *i32-max*))
           (equal (b* (((ok zc) (nnb-choose b x y))
                       ((ok z1) (i32-add (car zc) 1)))
                    (ok (nnb-apply-choose-back (cdr zc) z1)))
                  (if b
                      (ok (cons (+ x 1) y))
                    (ok (cons x (+ y 1))))))
  :rule-classes nil)

;; The write-through-borrow law in isolation: applying the backward
;; function of `choose` updates exactly the chosen component.

(defthm nnb-apply-choose-back-of-choose
  (equal (nnb-apply-choose-back (cdr (result-ok->val (nnb-choose b x y))) r)
         (if b (cons r y) (cons x r)))
  :rule-classes nil)
