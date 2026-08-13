; Phase 4 -- key-schedule decomposition support: length-only :ok / len /
; true-listp for the fold's shift-rows loops, and length/true-listp of the
; kround chain from the seed.
;
; The fold ops are pure gate/rotation networks (no data-dependent indexing),
; so their :ok needs only that the window is a len-8 true-list -- NOT a wstate.
; (The straight-line window ops' length-only facts -- sub_bytes, sub_bytes_nots,
; add_round_constant_bit -- live upstream in aes_fixslice_keyround, where the
; rcon-loop step equation needs them.)
(in-package "ACL2")
(include-book "aes_fixslice_keysched")
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))
(local (in-theory (disable len-when-wstatep true-listp-when-wstatep nth-when-zp)))

;; ===========================================================================
;; Length-only :ok and len for the four fold ops (values irrelevant to :ok).
;; ===========================================================================

;; primitives: fixed-shift shr never fails; delta-swap-1 (two fixed shifts) is ok.
(defthm result-kind-u32-shr-small
  (implies (and (natp n) (< n 32)) (equal (result-kind (u32-shr x n)) :ok)))
(defthm result-kind-of-delta-swap-1
  (implies (and (natp shift) (< shift 32))
           (equal (result-kind (aes-fixslice-encrypt-delta-swap-1 a shift mask)) :ok))
  :hints (("Goal" :in-theory (enable aes-fixslice-encrypt-delta-swap-1))))
(defthm val-of-delta-swap-1-when-ok
  (implies (and (natp shift) (< shift 32))
           (equal (result-ok->val (aes-fixslice-encrypt-delta-swap-1 a shift mask))
                  (u32-xor a (u32-xor (u32-and (u32-xor a (result-ok->val (u32-shr a shift))) mask)
                                      (result-ok->val (u32-shl (u32-and (u32-xor a (result-ok->val (u32-shr a shift))) mask) shift))))))
  :hints (("Goal" :in-theory (enable aes-fixslice-encrypt-delta-swap-1))))

;; ---- shift_rows_3 (= inv_shift_rows_1): a map over range 0..8; :ok and len ----
(local (include-book "std/lists/update-nth" :dir :system))
(defthm sr3-loop0-base
  (implies (and (natp i) (natp e) (<= e i) (not (zp n)))
           (equal (aes-fixslice-encrypt-shift-rows-3-loop0 n (rng i e) s) (ok s)))
  :hints (("Goal" :expand ((aes-fixslice-encrypt-shift-rows-3-loop0 n (rng i e) s))
           :in-theory (enable rnext-on-range))))
(defthm sr3-loop0-step
  (implies (and (natp i) (natp e) (< i e) (not (zp n)) (< i (len s)) (< (len s) 4294967296))
           (equal (aes-fixslice-encrypt-shift-rows-3-loop0 n (rng i e) s)
                  (aes-fixslice-encrypt-shift-rows-3-loop0 (1- n) (rng (+ i 1) e)
                    (update-nth i (result-ok->val (aes-fixslice-encrypt-delta-swap-1
                                    (result-ok->val (aes-fixslice-encrypt-delta-swap-1 (nth i s) 4 51317760))
                                    2 855651072)) s))))
  :hints (("Goal" :expand ((aes-fixslice-encrypt-shift-rows-3-loop0 n (rng i e) s))
           :in-theory (e/d (rnext-on-range) (aes-fixslice-encrypt-delta-swap-1)))))
(defun sr3-ind (n i e s)
  (declare (xargs :measure (nfix (- (nfix e) (nfix i)))))
  (if (and (natp i) (natp e) (< i e) (not (zp n)) (< i (len s)))
      (sr3-ind (1- n) (+ i 1) e
        (update-nth i (result-ok->val (aes-fixslice-encrypt-delta-swap-1
                        (result-ok->val (aes-fixslice-encrypt-delta-swap-1 (nth i s) 4 51317760))
                        2 855651072)) s))
    (list n i e s)))
(defthm result-kind-of-sr3-loop0
  (implies (and (natp i) (natp e) (<= i e) (< (len s) 4294967296) (<= e (len s)) (< (- e i) (nfix n)))
           (equal (result-kind (aes-fixslice-encrypt-shift-rows-3-loop0 n (rng i e) s)) :ok))
  :hints (("Goal" :induct (sr3-ind n i e s)
           :in-theory (disable aes-fixslice-encrypt-shift-rows-3-loop0 aes-fixslice-encrypt-delta-swap-1
                               (:executable-counterpart core-ops-range-range-usize-)))))
(defthm len-of-sr3-loop0
  (implies (and (natp i) (natp e) (<= i e) (< (len s) 4294967296) (<= e (len s)) (< (- e i) (nfix n)))
           (equal (len (result-ok->val (aes-fixslice-encrypt-shift-rows-3-loop0 n (rng i e) s))) (len s)))
  :hints (("Goal" :induct (sr3-ind n i e s)
           :in-theory (disable aes-fixslice-encrypt-shift-rows-3-loop0 aes-fixslice-encrypt-delta-swap-1
                               (:executable-counterpart core-ops-range-range-usize-)))))
(defthm result-kind-of-isr1-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (result-kind (aes-fixslice-encrypt-inv-shift-rows-1 100 s)) :ok))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-1 aes-fixslice-encrypt-shift-rows-3)
                                  (aes-fixslice-encrypt-shift-rows-3-loop0))
           :use (:instance result-kind-of-sr3-loop0 (i 0) (e 8) (n 100)))))
(defthm len-of-isr1-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (len (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1 100 s))) 8))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-1 aes-fixslice-encrypt-shift-rows-3)
                                  (aes-fixslice-encrypt-shift-rows-3-loop0))
           :use (:instance len-of-sr3-loop0 (i 0) (e 8) (n 100)))))

;; ---- shift_rows_2 (= inv_shift_rows_2): one delta-swap (mask 251662080) ----
(defthm sr2-loop0-base
  (implies (and (natp i) (natp e) (<= e i) (not (zp n)))
           (equal (aes-fixslice-encrypt-shift-rows-2-loop0 n (rng i e) s) (ok s)))
  :hints (("Goal" :expand ((aes-fixslice-encrypt-shift-rows-2-loop0 n (rng i e) s))
           :in-theory (enable rnext-on-range))))
(defthm sr2-loop0-step
  (implies (and (natp i) (natp e) (< i e) (not (zp n)) (< i (len s)) (< (len s) 4294967296))
           (equal (aes-fixslice-encrypt-shift-rows-2-loop0 n (rng i e) s)
                  (aes-fixslice-encrypt-shift-rows-2-loop0 (1- n) (rng (+ i 1) e)
                    (update-nth i (result-ok->val (aes-fixslice-encrypt-delta-swap-1 (nth i s) 4 251662080)) s))))
  :hints (("Goal" :expand ((aes-fixslice-encrypt-shift-rows-2-loop0 n (rng i e) s))
           :in-theory (e/d (rnext-on-range) (aes-fixslice-encrypt-delta-swap-1)))))
(defun sr2-ind (n i e s)
  (declare (xargs :measure (nfix (- (nfix e) (nfix i)))))
  (if (and (natp i) (natp e) (< i e) (not (zp n)) (< i (len s)))
      (sr2-ind (1- n) (+ i 1) e
        (update-nth i (result-ok->val (aes-fixslice-encrypt-delta-swap-1 (nth i s) 4 251662080)) s))
    (list n i e s)))
(defthm result-kind-of-sr2-loop0
  (implies (and (natp i) (natp e) (<= i e) (< (len s) 4294967296) (<= e (len s)) (< (- e i) (nfix n)))
           (equal (result-kind (aes-fixslice-encrypt-shift-rows-2-loop0 n (rng i e) s)) :ok))
  :hints (("Goal" :induct (sr2-ind n i e s)
           :in-theory (disable aes-fixslice-encrypt-shift-rows-2-loop0 aes-fixslice-encrypt-delta-swap-1
                               (:executable-counterpart core-ops-range-range-usize-)))))
(defthm len-of-sr2-loop0
  (implies (and (natp i) (natp e) (<= i e) (< (len s) 4294967296) (<= e (len s)) (< (- e i) (nfix n)))
           (equal (len (result-ok->val (aes-fixslice-encrypt-shift-rows-2-loop0 n (rng i e) s))) (len s)))
  :hints (("Goal" :induct (sr2-ind n i e s)
           :in-theory (disable aes-fixslice-encrypt-shift-rows-2-loop0 aes-fixslice-encrypt-delta-swap-1
                               (:executable-counterpart core-ops-range-range-usize-)))))
(defthm result-kind-of-isr2-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (result-kind (aes-fixslice-encrypt-inv-shift-rows-2 100 s)) :ok))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-2 aes-fixslice-encrypt-shift-rows-2)
                                  (aes-fixslice-encrypt-shift-rows-2-loop0))
           :use (:instance result-kind-of-sr2-loop0 (i 0) (e 8) (n 100)))))
(defthm len-of-isr2-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (len (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-2 100 s))) 8))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-2 aes-fixslice-encrypt-shift-rows-2)
                                  (aes-fixslice-encrypt-shift-rows-2-loop0))
           :use (:instance len-of-sr2-loop0 (i 0) (e 8) (n 100)))))

;; ---- shift_rows_1 (= inv_shift_rows_3): two delta-swaps (202310400, 855651072) ----
(defthm sr1-loop0-base
  (implies (and (natp i) (natp e) (<= e i) (not (zp n)))
           (equal (aes-fixslice-encrypt-shift-rows-1-loop0 n (rng i e) s) (ok s)))
  :hints (("Goal" :expand ((aes-fixslice-encrypt-shift-rows-1-loop0 n (rng i e) s))
           :in-theory (enable rnext-on-range))))
(defthm sr1-loop0-step
  (implies (and (natp i) (natp e) (< i e) (not (zp n)) (< i (len s)) (< (len s) 4294967296))
           (equal (aes-fixslice-encrypt-shift-rows-1-loop0 n (rng i e) s)
                  (aes-fixslice-encrypt-shift-rows-1-loop0 (1- n) (rng (+ i 1) e)
                    (update-nth i (result-ok->val (aes-fixslice-encrypt-delta-swap-1
                                    (result-ok->val (aes-fixslice-encrypt-delta-swap-1 (nth i s) 4 202310400))
                                    2 855651072)) s))))
  :hints (("Goal" :expand ((aes-fixslice-encrypt-shift-rows-1-loop0 n (rng i e) s))
           :in-theory (e/d (rnext-on-range) (aes-fixslice-encrypt-delta-swap-1)))))
(defun sr1-ind (n i e s)
  (declare (xargs :measure (nfix (- (nfix e) (nfix i)))))
  (if (and (natp i) (natp e) (< i e) (not (zp n)) (< i (len s)))
      (sr1-ind (1- n) (+ i 1) e
        (update-nth i (result-ok->val (aes-fixslice-encrypt-delta-swap-1
                        (result-ok->val (aes-fixslice-encrypt-delta-swap-1 (nth i s) 4 202310400))
                        2 855651072)) s))
    (list n i e s)))
(defthm result-kind-of-sr1-loop0
  (implies (and (natp i) (natp e) (<= i e) (< (len s) 4294967296) (<= e (len s)) (< (- e i) (nfix n)))
           (equal (result-kind (aes-fixslice-encrypt-shift-rows-1-loop0 n (rng i e) s)) :ok))
  :hints (("Goal" :induct (sr1-ind n i e s)
           :in-theory (disable aes-fixslice-encrypt-shift-rows-1-loop0 aes-fixslice-encrypt-delta-swap-1
                               (:executable-counterpart core-ops-range-range-usize-)))))
(defthm len-of-sr1-loop0
  (implies (and (natp i) (natp e) (<= i e) (< (len s) 4294967296) (<= e (len s)) (< (- e i) (nfix n)))
           (equal (len (result-ok->val (aes-fixslice-encrypt-shift-rows-1-loop0 n (rng i e) s))) (len s)))
  :hints (("Goal" :induct (sr1-ind n i e s)
           :in-theory (disable aes-fixslice-encrypt-shift-rows-1-loop0 aes-fixslice-encrypt-delta-swap-1
                               (:executable-counterpart core-ops-range-range-usize-)))))
(defthm result-kind-of-isr3-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (result-kind (aes-fixslice-encrypt-inv-shift-rows-3 100 s)) :ok))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-3 aes-fixslice-encrypt-shift-rows-1)
                                  (aes-fixslice-encrypt-shift-rows-1-loop0))
           :use (:instance result-kind-of-sr1-loop0 (i 0) (e 8) (n 100)))))
(defthm len-of-isr3-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (len (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-3 100 s))) 8))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-3 aes-fixslice-encrypt-shift-rows-1)
                                  (aes-fixslice-encrypt-shift-rows-1-loop0))
           :use (:instance len-of-sr1-loop0 (i 0) (e 8) (n 100)))))


;; true-listp for the isr ops (the shift-rows loops), so the write-back bridge
;; applies to their outputs.  Mirrors keydecomp's len lemmas.
(defthm true-listp-of-sr3-loop0
  (implies (and (natp i) (natp e) (<= i e) (< (len s) 4294967296) (<= e (len s))
                (< (- e i) (nfix n)) (true-listp s))
           (true-listp (result-ok->val (aes-fixslice-encrypt-shift-rows-3-loop0 n (rng i e) s))))
  :hints (("Goal" :induct (sr3-ind n i e s)
           :in-theory (disable aes-fixslice-encrypt-shift-rows-3-loop0 aes-fixslice-encrypt-delta-swap-1
                               (:executable-counterpart core-ops-range-range-usize-)))))
(defthm true-listp-of-sr2-loop0
  (implies (and (natp i) (natp e) (<= i e) (< (len s) 4294967296) (<= e (len s))
                (< (- e i) (nfix n)) (true-listp s))
           (true-listp (result-ok->val (aes-fixslice-encrypt-shift-rows-2-loop0 n (rng i e) s))))
  :hints (("Goal" :induct (sr2-ind n i e s)
           :in-theory (disable aes-fixslice-encrypt-shift-rows-2-loop0 aes-fixslice-encrypt-delta-swap-1
                               (:executable-counterpart core-ops-range-range-usize-)))))
(defthm true-listp-of-sr1-loop0
  (implies (and (natp i) (natp e) (<= i e) (< (len s) 4294967296) (<= e (len s))
                (< (- e i) (nfix n)) (true-listp s))
           (true-listp (result-ok->val (aes-fixslice-encrypt-shift-rows-1-loop0 n (rng i e) s))))
  :hints (("Goal" :induct (sr1-ind n i e s)
           :in-theory (disable aes-fixslice-encrypt-shift-rows-1-loop0 aes-fixslice-encrypt-delta-swap-1
                               (:executable-counterpart core-ops-range-range-usize-)))))
(defthm true-listp-of-isr1-100
  (implies (and (true-listp s) (equal (len s) 8))
           (true-listp (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1 100 s))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-1 aes-fixslice-encrypt-shift-rows-3)
                                  (aes-fixslice-encrypt-shift-rows-3-loop0))
           :use (:instance true-listp-of-sr3-loop0 (i 0) (e 8) (n 100)))))
(defthm true-listp-of-isr2-100
  (implies (and (true-listp s) (equal (len s) 8))
           (true-listp (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-2 100 s))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-2 aes-fixslice-encrypt-shift-rows-2)
                                  (aes-fixslice-encrypt-shift-rows-2-loop0))
           :use (:instance true-listp-of-sr2-loop0 (i 0) (e 8) (n 100)))))
(defthm true-listp-of-isr3-100
  (implies (and (true-listp s) (equal (len s) 8))
           (true-listp (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-3 100 s))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-3 aes-fixslice-encrypt-shift-rows-1)
                                  (aes-fixslice-encrypt-shift-rows-1-loop0))
           :use (:instance true-listp-of-sr1-loop0 (i 0) (e 8) (n 100)))))


;; ===========================================================================
;; kr-chain preserves length 88 and true-listp (needed so the fold ops apply).
;; Pure kround facts -- no invariant needed (kround-len / true-listp-of-kround
;; are length-only).
;; ===========================================================================
(defthm len-of-kr-chain
  (implies (and (natp i) (<= i 10) (equal off (* 8 i)) (equal (len rk) 88))
           (equal (len (kr-chain rk off i)) 88))
  :hints (("Goal" :induct (kr-chain rk off i)
           :in-theory (e/d (kr-chain) (kround rd8 nth wstatep)))))

(defthm true-listp-of-kr-chain
  (implies (true-listp rk) (true-listp (kr-chain rk off i)))
  :hints (("Goal" :induct (kr-chain rk off i)
           :in-theory (e/d (kr-chain) (kround rd8 nth wstatep)))))

;; length 88 and true-listp of the concrete core (kr-chain from the seed).
(defthm len-of-core
  (implies (aes::inp key)
           (equal (len (kr-chain (seed key) 0 0)) 88))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable kr-chain seed)
           :use (len-of-seed
                 (:instance len-of-kr-chain (rk (seed key)) (off 0) (i 0))))))
(defthm true-listp-of-core
  (implies (aes::inp key)
           (true-listp (kr-chain (seed key) 0 0)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable kr-chain seed)
           :use (true-listp-of-seed
                 (:instance true-listp-of-kr-chain (rk (seed key)))))))
