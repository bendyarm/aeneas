; Phase 4 -- key schedule CORE chain: SCAFFOLDING toward "the extracted 10
; key_rounds compute Kestrel's key expansion, bitsliced, for ALL inputs".
;
; The schedule seeds window 0 = bitslice(key,key) into an 88-word array and runs
; ten key_rounds, each writing the next 8-word window.  step-star (keystep) says
; one key_round advances a symmetric window bitslice(b,b) to bitslice(kr(b),kr(b));
; key-round-frame-below (keyround) says it leaves earlier windows untouched.  So
; every window r of the core array should be bitslice(kk_r,kk_r) with kk_r =
; kk-iter(key,r) the iterated recurrence -- i.e. the fixslice core computes
; Kestrel's key expansion, bitsliced.
;
; This book has the FOUNDATIONS ready and CERTIFIED:
;   step-star       : the c-uniform both-lanes-equal step (case-split of the ten
;                     keystep step-star-c)
;   inp-of-kk-iter  : the iterated recurrence stays an inp block (closure)
;   kx-byte         : the rcon column values are bytes
;   kr-chain, wok   : the recursive core model and the window invariant predicate
; and the read-over-write frame primitives are in aes_fixslice_keyframe.  The
; remaining array-threading inductions (5)-(7) are sketched at the end of the
; book; they are pure ACL2 induction plumbing over these ingredients.
(in-package "ACL2")
(include-book "aes_fixslice_keyframe")
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/append" :dir :system))
;; NB: no arithmetic-5 here -- its aggressive subtraction/nonlinear case splits
;; explode the wok inductions over the 8-strided window offsets.  ground-zero
;; linear arithmetic suffices for the (linear) offset reasoning; the rd8/
;; true-listp frame lemmas that DO want arithmetic-5 live in aes_fixslice_keyframe.
(local (in-theory (disable len-when-wstatep true-listp-when-wstatep)))

;; ---------------------------------------------------------------------------
;; (1) unified step: one key_round advances a symmetric window, for variable
;; rcon index c in 0..9.  Case-splits to the ten concrete step-star-c.
(defthm step-star
  (implies (and (aes::inp b) (natp c) (< c 10))
           (equal (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice b b)) c)
                  (result-ok->val (aes-fixslice-encrypt-bitslice
                                    (kr-spec-bytes b (kx c)) (kr-spec-bytes b (kx c))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable krw8 aes-fixslice-encrypt-bitslice kr-spec-bytes kx)
           :cases ((equal c 0) (equal c 1) (equal c 2) (equal c 3) (equal c 4)
                   (equal c 5) (equal c 6) (equal c 7) (equal c 8) (equal c 9))
           :use (step-star-0-general step-star-1-general step-star-2-general
                 step-star-3-general step-star-4-general step-star-5-general
                 step-star-6-general step-star-7-general step-star-8-general
                 step-star-9-general))))

;; ---------------------------------------------------------------------------
;; (2) the rcon column values are bytes, and kk-iter stays an inp block.
(defthm kx-byte
  (implies (and (natp c) (< c 10)) (unsigned-byte-p 8 (kx c)))
  :hints (("Goal" :in-theory (enable kx)
           :cases ((equal c 0) (equal c 1) (equal c 2) (equal c 3) (equal c 4)
                   (equal c 5) (equal c 6) (equal c 7) (equal c 8) (equal c 9)))))

(defthm inp-of-kk-iter
  (implies (and (aes::inp key) (natp r) (<= r 10))
           (aes::inp (kk-iter key r)))
  :hints (("Goal" :induct (kk-iter key r)
           :in-theory (e/d (kk-iter) (kr-spec-bytes kx)))
          '(:use ((:instance inp-of-kr-spec-bytes
                    (b (kk-iter key (1- r))) (rv (kx (1- r))))
                  (:instance kx-byte (c (1- r)))))))

;; ---------------------------------------------------------------------------
;; (4) the recursive core model (threads the offset exactly as the extracted
;; schedule does: off_{i+1} = car of round i) and the window invariant.
(defun kr-chain (rk off i)
  (declare (xargs :measure (nfix (- 10 i))))
  (if (or (not (natp i)) (>= i 10)) rk
    (b* ((res (result-ok->val (aes-fixslice-encrypt-key-round 100 rk off i))))
      (kr-chain (cdr res) (car res) (1+ i)))))

;; wok rk key off i  <=>  window i is at byte-offset off and equals bitslice(kk_i,kk_i),
;; window i-1 at off-8, ... down to window 0 at off-8i.  off and i decrement in
;; lockstep (off by 8, i by 1), so NO (* 8 i) appears inside the induction --
;; the caller supplies off = 8i, keeping all offset arithmetic linear.
(defun wok (rk key off i)
  (declare (xargs :measure (nfix i)))
  (if (zp i)
      (equal (rd8 rk off)
             (result-ok->val (aes-fixslice-encrypt-bitslice (kk-iter key 0) (kk-iter key 0))))
    (and (equal (rd8 rk off)
                (result-ok->val (aes-fixslice-encrypt-bitslice (kk-iter key i) (kk-iter key i))))
         (wok rk key (nfix (- off 8)) (1- i)))))

;; ---------------------------------------------------------------------------
;; REMAINING (the array-threading assembly).  With the pieces above the core
;; chain reduces to pure read-over-write bookkeeping:
;;
;;   (5) wok-of-key-round-below : a key_round at off0 preserves every window at
;;       or below off0 -- an induction over wok using rd8-of-key-round-below
;;       (keyframe) at the top window and the IH for the tail.
;;   (6) wok-of-key-round : it also EXTENDS the invariant by one window --
;;       rd8(new, off0+8) = krw8(rd8 rkeys off0, c) [key-round-window]
;;                        = bitslice(kk_{i+1},kk_{i+1}) [step-star + inp-of-kk-iter].
;;   (7) kr-chain-wok : threading (5)+(6) through kr-chain (off = 8i maintained
;;       by key-round-car) gives wok(kr-chain(seed,0,0), key, 80, 10): every core
;;       window r = bitslice(kk_r,kk_r), all inputs.
;;
;; step-star, inp-of-kk-iter, key-round-window/-car/-frame-below, and the keyframe
;; frame lemmas are the ingredients; what is left is the ACL2 induction plumbing
;; to combine them (fiddly: the offset inductions are sensitive to arithmetic-5,
;; hence the deliberate no-arith5 setting and the linear off/i formulation of wok).
;; The fold layer (keyschedule per-op facts) then adjusts each window to fk(r).
