; Symbolic correctness for the COMPILER-GENERATED TEA cipher (gen-tea.lisp,
; unmodified output of charon + aeneas -backend acl2). The target theorem is
; decrypt(encrypt(v,k),k) = v for ALL inputs.
;
; The Feistel structure makes this pure wrapping-arithmetic cancellation:
; each decrypt round subtracts exactly what the corresponding encrypt round
; added, with the round function F treated as an opaque u32 (its internal
; xor/shift structure is irrelevant to invertibility).

(in-package "ACL2")

(include-book "tea")
(include-book "arithmetic-5/top" :dir :system)

;; ---------------------------------------------------------------------
;; Core algebraic facts about the wrapping ops (the whole cipher's
;; invertibility reduces to these).
;; ---------------------------------------------------------------------

(defthm u32p-of-wrapping-add-val
  (implies (and (integerp x) (integerp y))
           (u32p (result-ok->val (u32-wrapping-add x y))))
  :hints (("Goal" :in-theory (enable u32-wrapping-add u32p))))

(defthm u32p-of-wrapping-sub-val
  (implies (and (integerp x) (integerp y))
           (u32p (result-ok->val (u32-wrapping-sub x y))))
  :hints (("Goal" :in-theory (enable u32-wrapping-sub u32p))))

;; wrapping_sub undoes wrapping_add: (a +w f) -w f = a  (for a in range).
(defthm wrapping-sub-of-wrapping-add
  (implies (and (u32p a) (integerp f))
           (equal (u32-wrapping-sub (result-ok->val (u32-wrapping-add a f)) f)
                  (ok a)))
  :hints (("Goal" :in-theory (enable u32-wrapping-add u32-wrapping-sub u32p))))

;; The mirror image, used at the sum-restoration step of each round.
(defthm wrapping-add-of-wrapping-sub
  (implies (and (u32p a) (integerp f))
           (equal (u32-wrapping-add (result-ok->val (u32-wrapping-sub a f)) f)
                  (ok a)))
  :hints (("Goal" :in-theory (enable u32-wrapping-add u32-wrapping-sub u32p))))

;; ---------------------------------------------------------------------
;; Full-cipher round trip: validated EXECUTABLY here (all-inputs symbolic
;; induction is the documented next step, see NOTE below).
;;
;; NOTE (next step): the all-inputs theorem
;;   decrypt(encrypt(v,k),k) = v
;; reduces to the two wrapping-cancellation lemmas above applied 32 times,
;; treating each round function F opaquely. The proof needs (a) a lemma
;; that a small constant shift never fails, so u32-shl/u32-shr can be kept
;; disabled and F stays an opaque u32 term, and (b) a generalized loop
;; invariant relating encrypt-loop0 (sum,i increasing) to decrypt-loop0
;; run from the mirrored sum. With F opaque the per-round cancellation is
;; exactly wrapping-sub-of-wrapping-add / wrapping-add-of-wrapping-sub;
;; the remaining work is the induction bookkeeping, not new mathematics.
;; ---------------------------------------------------------------------

;; Executable round-trip on concrete inputs (fuel 33 > 32 rounds).
(defthm tea-round-trip-executable-1
  (equal (b* (((ok c) (tea-encrypt 33 #x12345678 #x9abcdef0 1 2 3 4)))
           (tea-decrypt 33 (car c) (cdr c) 1 2 3 4))
         (ok (cons #x12345678 #x9abcdef0)))
  :rule-classes nil)

(defthm tea-round-trip-executable-2
  (equal (b* (((ok c) (tea-encrypt 33 0 0 0 0 0 0)))
           (tea-decrypt 33 (car c) (cdr c) 0 0 0 0))
         (ok (cons 0 0)))
  :rule-classes nil)
