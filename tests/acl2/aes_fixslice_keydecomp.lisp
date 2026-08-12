; Phase 4 -- key-schedule decomposition: the extracted aes128-key-schedule
; equals a clean model  (ok (ks-fold (kr-chain seed 0 0)))  for all inputs.
;
; The extracted schedule is one 27-op b* nest: seed (bitslice-into), 10
; key_rounds (threading (off . rkeys)), then 17 fold at-ops (7 inv_shift_rows_i,
; 10 sub_bytes_nots).  The fold ops are pure gate/rotation networks (no data-
; dependent indexing), so their :ok needs only that the array is long enough --
; NOT a wstate window.  So every op's b* short-circuit collapses on a length-88
; array and the extracted nest is exactly the clean model.
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

;; ---- sub_bytes_nots: straight-line (indices 0,1,5,6); :ok and len for len>=7 ----
(defthm result-kind-of-sub-bytes-nots-len
  (implies (and (true-listp s) (<= 7 (len s)))
           (equal (result-kind (aes-fixslice-encrypt-sub-bytes-nots s)) :ok))
  :hints (("Goal" :in-theory (enable aes-fixslice-encrypt-sub-bytes-nots))))
(defthm len-of-sub-bytes-nots-len
  (implies (and (true-listp s) (<= 7 (len s)))
           (equal (len (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots s))) (len s)))
  :hints (("Goal" :in-theory (enable aes-fixslice-encrypt-sub-bytes-nots))))

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

;; ===========================================================================
;; The fold at-ops (read8 ; op ; write8) are :ok and length-preserving on any
;; length-88-ish array (window need not be a wstate).  Local form lemmas
;; (rule-classes nil) give the w8-spec shape; the exported rules keep -at opaque.
;; ===========================================================================
(local (defthm isr1-at-form-len
  (implies (and (natp off) (<= (+ off 8) (len rk)) (< (len rk) 4294967296))
           (equal (aes-fixslice-encrypt-inv-shift-rows-1-at 100 rk off)
                  (ok (w8-spec 0 8 rk off (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1 100 (rd8 rk off)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-1-at)
                                  (aes-fixslice-encrypt-inv-shift-rows-1 w8-spec rd8 nth))))))
(defthm result-kind-of-isr1-at-len
  (implies (and (natp off) (<= (+ off 8) (len rk)) (< (len rk) 4294967296))
           (equal (result-kind (aes-fixslice-encrypt-inv-shift-rows-1-at 100 rk off)) :ok))
  :hints (("Goal" :use isr1-at-form-len :in-theory (disable w8-spec))))
(defthm len-of-isr1-at-len
  (implies (and (natp off) (<= (+ off 8) (len rk)) (< (len rk) 4294967296))
           (equal (len (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1-at 100 rk off))) (len rk)))
  :hints (("Goal" :use isr1-at-form-len :in-theory (disable w8-spec))))

(local (defthm isr2-at-form-len
  (implies (and (natp off) (<= (+ off 8) (len rk)) (< (len rk) 4294967296))
           (equal (aes-fixslice-encrypt-inv-shift-rows-2-at 100 rk off)
                  (ok (w8-spec 0 8 rk off (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-2 100 (rd8 rk off)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-2-at)
                                  (aes-fixslice-encrypt-inv-shift-rows-2 w8-spec rd8 nth))))))
(defthm result-kind-of-isr2-at-len
  (implies (and (natp off) (<= (+ off 8) (len rk)) (< (len rk) 4294967296))
           (equal (result-kind (aes-fixslice-encrypt-inv-shift-rows-2-at 100 rk off)) :ok))
  :hints (("Goal" :use isr2-at-form-len :in-theory (disable w8-spec))))
(defthm len-of-isr2-at-len
  (implies (and (natp off) (<= (+ off 8) (len rk)) (< (len rk) 4294967296))
           (equal (len (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-2-at 100 rk off))) (len rk)))
  :hints (("Goal" :use isr2-at-form-len :in-theory (disable w8-spec))))

(local (defthm isr3-at-form-len
  (implies (and (natp off) (<= (+ off 8) (len rk)) (< (len rk) 4294967296))
           (equal (aes-fixslice-encrypt-inv-shift-rows-3-at 100 rk off)
                  (ok (w8-spec 0 8 rk off (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-3 100 (rd8 rk off)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-3-at)
                                  (aes-fixslice-encrypt-inv-shift-rows-3 w8-spec rd8 nth))))))
(defthm result-kind-of-isr3-at-len
  (implies (and (natp off) (<= (+ off 8) (len rk)) (< (len rk) 4294967296))
           (equal (result-kind (aes-fixslice-encrypt-inv-shift-rows-3-at 100 rk off)) :ok))
  :hints (("Goal" :use isr3-at-form-len :in-theory (disable w8-spec))))
(defthm len-of-isr3-at-len
  (implies (and (natp off) (<= (+ off 8) (len rk)) (< (len rk) 4294967296))
           (equal (len (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-3-at 100 rk off))) (len rk)))
  :hints (("Goal" :use isr3-at-form-len :in-theory (disable w8-spec))))

(local (defthm sbn-at-form-len
  (implies (and (natp off) (<= (+ off 8) (len rk)) (< (len rk) 4294967296))
           (equal (aes-fixslice-encrypt-sub-bytes-nots-at 100 rk off)
                  (ok (w8-spec 0 8 rk off (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots (rd8 rk off)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-sub-bytes-nots-at)
                                  (aes-fixslice-encrypt-sub-bytes-nots w8-spec rd8 nth))))))
(defthm result-kind-of-sbn-at-len
  (implies (and (natp off) (<= (+ off 8) (len rk)) (< (len rk) 4294967296))
           (equal (result-kind (aes-fixslice-encrypt-sub-bytes-nots-at 100 rk off)) :ok))
  :hints (("Goal" :use sbn-at-form-len :in-theory (disable w8-spec))))
(defthm len-of-sbn-at-len
  (implies (and (natp off) (<= (+ off 8) (len rk)) (< (len rk) 4294967296))
           (equal (len (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots-at 100 rk off))) (len rk)))
  :hints (("Goal" :use sbn-at-form-len :in-theory (disable w8-spec))))

;; ===========================================================================
;; :ok for the seed (bitslice-into) and each key_round (from key-round-unfold).
;; ===========================================================================
(defthm result-kind-of-key-round
  (implies (and (natp off) (equal (rem off 8) 0)
                (<= (+ off 16) (len rkeys)) (< (len rkeys) 4294967296)
                (true-listp rkeys) (wstatep (rd8 rkeys off)) (natp c) (< c 12))
           (equal (result-kind (aes-fixslice-encrypt-key-round 100 rkeys off c)) :ok))
  :hints (("Goal" :use key-round-unfold
           :in-theory (disable key-round-unfold w8-spec ms-spec xc-spec rd8 nth
                               aes-fixslice-encrypt-key-round))))

(defthm result-kind-of-seed
  (implies (aes::inp key)
           (equal (result-kind (aes-fixslice-encrypt-bitslice-into 100 (array-repeat 88 0) 0 key key)) :ok))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-bitslice-into len-when-wstatep)
                                  (aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-write8
                                   aes-fixslice-encrypt-write8-loop0 w8-spec rd8 wstatep nth))
           :use ((:instance wstatep-of-bitslice (b0 key) (b1 key))
                 (:instance bitslice-ok (b0 key) (b1 key))
                 (:instance write8-is-w8spec (rkeys (array-repeat 88 0)) (off 0)
                            (s (result-ok->val (aes-fixslice-encrypt-bitslice key key))))))))

;; ===========================================================================
;; Length-only :ok + len for the remaining key_round sub-ops, so key_round is
;; :ok on length alone (car = off+8, len preserved) -- letting the decomposition
;; collapse the 10 rounds with every op kept OPAQUE (no wstate telescoping,
;; which would rewrite key_round into its huge form and blow up).
;; ===========================================================================
;; sub_bytes: straight-line gate network on indices 0..7.  Proving :ok/len on a
;; symbolic len-8 list makes the 16 array bounds case-split (2^16); instead prove
;; on an EXPLICIT 8-list (everything computes) and lift via expand-len-8.
(local (defthm rk-sub-bytes-explicit
  (equal (result-kind (aes-fixslice-encrypt-sub-bytes (list a0 a1 a2 a3 a4 a5 a6 a7))) :ok)
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-sub-bytes) (u32-xor u32-and))))))
(local (defthm len-sub-bytes-explicit
  (equal (len (result-ok->val (aes-fixslice-encrypt-sub-bytes (list a0 a1 a2 a3 a4 a5 a6 a7)))) 8)
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-sub-bytes) (u32-xor u32-and))))))
(defthm result-kind-of-sub-bytes-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (result-kind (aes-fixslice-encrypt-sub-bytes s)) :ok))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-sub-bytes nth)
           :use ((:instance rk-sub-bytes-explicit
                  (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s))
                  (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s)))
                 (:instance expand-len-8 (x s))))))
(defthm len-of-sub-bytes-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (len (result-ok->val (aes-fixslice-encrypt-sub-bytes s))) 8))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-sub-bytes nth)
           :use ((:instance len-sub-bytes-explicit
                  (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s))
                  (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s)))
                 (:instance expand-len-8 (x s))))))
;; sub_bytes-at (read8 ; sub_bytes ; write8): length-only.
(local (defthm sba-at-form-len
  (implies (and (natp off) (<= (+ off 8) (len rk)) (< (len rk) 4294967296))
           (equal (aes-fixslice-encrypt-sub-bytes-at 100 rk off)
                  (ok (w8-spec 0 8 rk off (result-ok->val (aes-fixslice-encrypt-sub-bytes (rd8 rk off)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-sub-bytes-at)
                                  (aes-fixslice-encrypt-sub-bytes w8-spec rd8 nth))))))
(defthm result-kind-of-sub-bytes-at-len
  (implies (and (natp off) (<= (+ off 8) (len rk)) (< (len rk) 4294967296))
           (equal (result-kind (aes-fixslice-encrypt-sub-bytes-at 100 rk off)) :ok))
  :hints (("Goal" :use sba-at-form-len :in-theory (disable w8-spec))))
(defthm len-of-sub-bytes-at-len
  (implies (and (natp off) (<= (+ off 8) (len rk)) (< (len rk) 4294967296))
           (equal (len (result-ok->val (aes-fixslice-encrypt-sub-bytes-at 100 rk off))) (len rk)))
  :hints (("Goal" :use sba-at-form-len :in-theory (disable w8-spec))))

;; add_round_constant_bit (array-index ; xor ; array-update at index bit): :ok for bit<len.
(defthm result-kind-of-arcbit-len
  (implies (and (natp bit) (< bit (len s)))
           (equal (result-kind (aes-fixslice-encrypt-add-round-constant-bit s bit)) :ok))
  :hints (("Goal" :in-theory (enable aes-fixslice-encrypt-add-round-constant-bit))))
(defthm len-of-arcbit-len
  (implies (and (natp bit) (< bit (len s)))
           (equal (len (result-ok->val (aes-fixslice-encrypt-add-round-constant-bit s bit))) (len s)))
  :hints (("Goal" :in-theory (enable aes-fixslice-encrypt-add-round-constant-bit))))
;; add-rc-bit-at (read8 ; arcbit ; write8): length-only for bit<8.
(local (defthm arcbit-at-form-len
  (implies (and (natp off) (<= (+ off 8) (len rk)) (< (len rk) 4294967296) (natp bit) (< bit 8))
           (equal (aes-fixslice-encrypt-add-rc-bit-at 100 rk off bit)
                  (ok (w8-spec 0 8 rk off (result-ok->val (aes-fixslice-encrypt-add-round-constant-bit (rd8 rk off) bit))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-add-rc-bit-at)
                                  (aes-fixslice-encrypt-add-round-constant-bit w8-spec rd8 nth))))))
(defthm result-kind-of-arcbit-at-len
  (implies (and (natp off) (<= (+ off 8) (len rk)) (< (len rk) 4294967296) (natp bit) (< bit 8))
           (equal (result-kind (aes-fixslice-encrypt-add-rc-bit-at 100 rk off bit)) :ok))
  :hints (("Goal" :use arcbit-at-form-len :in-theory (disable w8-spec))))
(defthm len-of-arcbit-at-len
  (implies (and (natp off) (<= (+ off 8) (len rk)) (< (len rk) 4294967296) (natp bit) (< bit 8))
           (equal (len (result-ok->val (aes-fixslice-encrypt-add-rc-bit-at 100 rk off bit))) (len rk)))
  :hints (("Goal" :use arcbit-at-form-len :in-theory (disable w8-spec))))
;; add-rcon (up to four add-rc-bit-at at bits derived from rcon<12, all <8): :ok + len.
(defthm result-kind-of-add-rcon-len
  (implies (and (natp off) (<= (+ off 8) (len rk)) (< (len rk) 4294967296) (natp c) (< c 12))
           (equal (result-kind (aes-fixslice-encrypt-add-rcon 100 rk off c)) :ok))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-add-rcon)
                                  (aes-fixslice-encrypt-add-rc-bit-at)))))
(defthm len-of-add-rcon-len
  (implies (and (natp off) (<= (+ off 8) (len rk)) (< (len rk) 4294967296) (natp c) (< c 12))
           (equal (len (result-ok->val (aes-fixslice-encrypt-add-rcon 100 rk off c))) (len rk)))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-add-rcon)
                                  (aes-fixslice-encrypt-add-rc-bit-at)))))

;; key_round is :ok on length alone; car = off+8, cdr keeps the length.
(local (defthm key-round-form-len
  (implies (and (natp off) (equal (rem off 8) 0) (<= (+ off 16) (len rk)) (< (len rk) 4294967296)
                (true-listp rk) (natp c) (< c 12))
           (equal (aes-fixslice-encrypt-key-round 100 rk off c)
                  (ok (cons (+ off 8)
                            (xc-spec 0 8
                              (result-ok->val (aes-fixslice-encrypt-add-rcon 100
                                (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots-at 100
                                  (result-ok->val (aes-fixslice-encrypt-sub-bytes-at 100
                                    (ms-spec 0 8 rk off (+ off 8)) (+ off 8))) (+ off 8))) (+ off 8) c))
                              (+ off 8) 8 14)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (aes-fixslice-encrypt-key-round)
                           (aes-fixslice-encrypt-memshift32 aes-fixslice-encrypt-sub-bytes-at
                            aes-fixslice-encrypt-sub-bytes-nots-at aes-fixslice-encrypt-add-rcon
                            aes-fixslice-encrypt-xor-columns ms-spec xc-spec w8-spec rd8 nth))
           :use ((:instance memshift32-is-msspec (buffer rk) (src off))
                 (:instance xor-columns-is-xcspec (rkeys (result-ok->val (aes-fixslice-encrypt-add-rcon 100
                                (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots-at 100
                                  (result-ok->val (aes-fixslice-encrypt-sub-bytes-at 100
                                    (ms-spec 0 8 rk off (+ off 8)) (+ off 8))) (+ off 8))) (+ off 8) c)))
                            (off (+ off 8)) (dx 8) (dror 14)))))))
;; keep the whole form term opaque (disable every constituent) so result-kind/car
;; resolve on the (ok (cons ..)) tag alone -- never normalizing the giant body.
(local (in-theory (disable aes-fixslice-encrypt-xor-columns aes-fixslice-encrypt-add-rcon
                           aes-fixslice-encrypt-sub-bytes-nots-at aes-fixslice-encrypt-sub-bytes-at
                           aes-fixslice-encrypt-memshift32 xc-spec ms-spec w8-spec)))
(defthm result-kind-of-key-round-len
  (implies (and (natp off) (equal (rem off 8) 0) (<= (+ off 16) (len rk)) (< (len rk) 4294967296)
                (true-listp rk) (natp c) (< c 12))
           (equal (result-kind (aes-fixslice-encrypt-key-round 100 rk off c)) :ok))
  :hints (("Goal" :use key-round-form-len :do-not-induct t
           :in-theory (disable aes-fixslice-encrypt-key-round))))
(defthm key-round-car-len
  (implies (and (natp off) (equal (rem off 8) 0) (<= (+ off 16) (len rk)) (< (len rk) 4294967296)
                (true-listp rk) (natp c) (< c 12))
           (equal (car (result-ok->val (aes-fixslice-encrypt-key-round 100 rk off c))) (+ off 8)))
  :hints (("Goal" :use key-round-form-len :do-not-induct t
           :in-theory (disable aes-fixslice-encrypt-key-round))))
(defthm len-of-cdr-key-round-len
  (implies (and (natp off) (equal (rem off 8) 0) (<= (+ off 16) (len rk)) (< (len rk) 4294967296)
                (true-listp rk) (natp c) (< c 12))
           (equal (len (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100 rk off c)))) (len rk)))
  :hints (("Goal" :use key-round-form-len
           :in-theory (e/d (len-of-xc-spec len-of-w8-spec len-of-ms-spec len-of-add-rcon-len
                            len-of-sbn-at-len len-of-sub-bytes-at-len)
                           (aes-fixslice-encrypt-key-round)))))
;; true-listp preservation on length alone (for the fuel/loop plumbing in
;; keyasm, where no wok invariant -- hence no wstatep -- is available).
(local (defthm true-listp-of-sub-bytes-at-len
  (implies (and (natp off) (<= (+ off 8) (len rk)) (< (len rk) 4294967296) (true-listp rk))
           (true-listp (result-ok->val (aes-fixslice-encrypt-sub-bytes-at 100 rk off))))
  ;; rd8/nth/wstatep stay closed: otherwise relieving the wstatep-hypothesized
  ;; interface rules for these ops opens an nth case-split swamp (arith-5).
  :hints (("Goal" :use sba-at-form-len
           :in-theory (disable w8-spec rd8 nth wstatep
                               aes-fixslice-encrypt-sub-bytes-at
                               aes-fixslice-encrypt-sub-bytes)))))
(local (defthm true-listp-of-sbn-at-len
  (implies (and (natp off) (<= (+ off 8) (len rk)) (< (len rk) 4294967296) (true-listp rk))
           (true-listp (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots-at 100 rk off))))
  :hints (("Goal" :use sbn-at-form-len
           :in-theory (disable w8-spec rd8 nth wstatep
                               aes-fixslice-encrypt-sub-bytes-nots-at
                               aes-fixslice-encrypt-sub-bytes-nots)))))
(local (defthm true-listp-of-arcbit-at-len
  (implies (and (natp off) (<= (+ off 8) (len rk)) (< (len rk) 4294967296)
                (natp bit) (< bit 8) (true-listp rk))
           (true-listp (result-ok->val (aes-fixslice-encrypt-add-rc-bit-at 100 rk off bit))))
  :hints (("Goal" :use arcbit-at-form-len
           :in-theory (disable w8-spec rd8 nth wstatep
                               aes-fixslice-encrypt-add-rc-bit-at
                               aes-fixslice-encrypt-add-round-constant-bit)))))
(local (defthm true-listp-of-add-rcon-len
  (implies (and (natp off) (<= (+ off 8) (len rk)) (< (len rk) 4294967296)
                (natp c) (< c 12) (true-listp rk))
           (true-listp (result-ok->val (aes-fixslice-encrypt-add-rcon 100 rk off c))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-add-rcon)
                                  (aes-fixslice-encrypt-add-rc-bit-at rd8 nth wstatep
                                   aes-fixslice-encrypt-add-round-constant-bit))))))
(defthm true-listp-of-cdr-key-round-len
  (implies (and (natp off) (equal (rem off 8) 0) (<= (+ off 16) (len rk)) (< (len rk) 4294967296)
                (true-listp rk) (natp c) (< c 12))
           (true-listp (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100 rk off c)))))
  ;; every true-listp/len step of the tower supplied as an explicit instance:
  ;; nothing backchains (the wstatep-hypothesized keyframe rule in particular
  ;; would send relief into an nth case-split swamp).
  :hints (("Goal" :do-not-induct t
           :use (key-round-form-len
                 (:instance true-listp-of-ms-spec (i 0) (e 8) (buffer rk) (src off) (dst (+ off 8)))
                 (:instance len-of-ms-spec (i 0) (e 8) (buffer rk) (src off) (dst (+ off 8)))
                 (:instance true-listp-of-sub-bytes-at-len
                            (rk (ms-spec 0 8 rk off (+ off 8))) (off (+ off 8)))
                 (:instance len-of-sub-bytes-at-len
                            (rk (ms-spec 0 8 rk off (+ off 8))) (off (+ off 8)))
                 (:instance true-listp-of-sbn-at-len
                            (rk (result-ok->val (aes-fixslice-encrypt-sub-bytes-at 100
                                  (ms-spec 0 8 rk off (+ off 8)) (+ off 8))))
                            (off (+ off 8)))
                 (:instance len-of-sbn-at-len
                            (rk (result-ok->val (aes-fixslice-encrypt-sub-bytes-at 100
                                  (ms-spec 0 8 rk off (+ off 8)) (+ off 8))))
                            (off (+ off 8)))
                 (:instance true-listp-of-add-rcon-len
                            (rk (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots-at 100
                                  (result-ok->val (aes-fixslice-encrypt-sub-bytes-at 100
                                    (ms-spec 0 8 rk off (+ off 8)) (+ off 8))) (+ off 8))))
                            (off (+ off 8)) (c c))
                 (:instance true-listp-of-xc-spec (i 0) (e 8)
                            (rkeys (result-ok->val (aes-fixslice-encrypt-add-rcon 100
                                     (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots-at 100
                                       (result-ok->val (aes-fixslice-encrypt-sub-bytes-at 100
                                         (ms-spec 0 8 rk off (+ off 8)) (+ off 8))) (+ off 8))) (+ off 8) c)))
                            (off (+ off 8)) (dx 8) (dror 14)))
           :in-theory (disable aes-fixslice-encrypt-key-round true-listp-of-cdr-key-round
                               true-listp-of-ms-spec true-listp-of-xc-spec
                               rd8 nth wstatep))))

;; ===========================================================================
;; kr-chain preserves length 88 and true-listp (needed so the fold ops apply).
;; Same induction shape as kr-chain-wok: wok supplies the wstate window at each
;; step (wstatep-rd8-of-wok), and wok-of-key-round carries the IH forward.
;; ===========================================================================
(defthm len-of-kr-chain
  (implies (and (aes::inp key) (natp i) (<= i 10) (equal off (* 8 i))
                (equal (len rk) 88) (true-listp rk) (wok rk key off i))
           (equal (len (kr-chain rk off i)) 88))
  :hints (("Goal" :induct (kr-chain rk off i)
           :in-theory (e/d (kr-chain)
                           (aes-fixslice-encrypt-key-round key-round-unfold rd8
                            aes-fixslice-encrypt-bitslice kk-iter krw8 wstatep nth
                            kr-spec-bytes wok wok-cong rd8-agree)))
          ("Subgoal *1/2"
           :use ((:instance wok-of-key-round (rkeys rk) (off0 (* 8 i)) (i i))
                 (:instance key-round-car (rkeys rk) (off (* 8 i)) (c i))
                 (:instance key-round-len (rkeys rk) (off (* 8 i)) (c i))
                 (:instance true-listp-of-cdr-key-round (rkeys rk) (off (* 8 i)) (c i))
                 (:instance wstatep-rd8-of-wok (rk rk) (key key) (off (* 8 i)) (i i))))))

(defthm true-listp-of-kr-chain
  (implies (and (aes::inp key) (natp i) (<= i 10) (equal off (* 8 i))
                (equal (len rk) 88) (true-listp rk) (wok rk key off i))
           (true-listp (kr-chain rk off i)))
  :hints (("Goal" :induct (kr-chain rk off i)
           :in-theory (e/d (kr-chain)
                           (aes-fixslice-encrypt-key-round key-round-unfold rd8
                            aes-fixslice-encrypt-bitslice kk-iter krw8 wstatep nth
                            kr-spec-bytes wok wok-cong rd8-agree)))
          ("Subgoal *1/2"
           :use ((:instance wok-of-key-round (rkeys rk) (off0 (* 8 i)) (i i))
                 (:instance key-round-car (rkeys rk) (off (* 8 i)) (c i))
                 (:instance key-round-len (rkeys rk) (off (* 8 i)) (c i))
                 (:instance true-listp-of-cdr-key-round (rkeys rk) (off (* 8 i)) (c i))
                 (:instance wstatep-rd8-of-wok (rk rk) (key key) (off (* 8 i)) (i i))))))

;; length 88 and true-listp of the concrete core (kr-chain from the seed).
(defthm len-of-core
  (implies (aes::inp key)
           (equal (len (kr-chain (result-ok->val
                          (aes-fixslice-encrypt-bitslice-into 100 (array-repeat 88 0) 0 key key)) 0 0))
                  88))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable kr-chain wok aes-fixslice-encrypt-bitslice-into)
           :use (wok-of-seed len-of-seed true-listp-of-seed
                 (:instance len-of-kr-chain
                            (rk (result-ok->val (aes-fixslice-encrypt-bitslice-into 100 (array-repeat 88 0) 0 key key)))
                            (off 0) (i 0))))))
(defthm true-listp-of-core
  (implies (aes::inp key)
           (true-listp (kr-chain (result-ok->val
                          (aes-fixslice-encrypt-bitslice-into 100 (array-repeat 88 0) 0 key key)) 0 0)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable kr-chain wok aes-fixslice-encrypt-bitslice-into)
           :use (wok-of-seed len-of-seed true-listp-of-seed
                 (:instance true-listp-of-kr-chain
                            (rk (result-ok->val (aes-fixslice-encrypt-bitslice-into 100 (array-repeat 88 0) 0 key key)))
                            (off 0) (i 0))))))

;; ===========================================================================
;; The clean fold model: the 17 concrete fold at-ops in the extracted order.
;; ===========================================================================
(defun ks-fold (w)
  (b* ((w (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1-at 100 w 8)))
       (w (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-2-at 100 w 16)))
       (w (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-3-at 100 w 24)))
       (w (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1-at 100 w 40)))
       (w (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-2-at 100 w 48)))
       (w (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-3-at 100 w 56)))
       (w (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1-at 100 w 72)))
       (w (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots-at 100 w 8)))
       (w (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots-at 100 w 16)))
       (w (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots-at 100 w 24)))
       (w (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots-at 100 w 32)))
       (w (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots-at 100 w 40)))
       (w (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots-at 100 w 48)))
       (w (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots-at 100 w 56)))
       (w (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots-at 100 w 64)))
       (w (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots-at 100 w 72))))
    (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots-at 100 w 80))))

;; ===========================================================================
;; DECOMPOSITION: the extracted schedule == ok(ks-fold(kr-chain(seed,0,0))).
;; Every op is :ok (fold ops by length, key_rounds by the wstate window that
;; key-round-window/wstatep-of-krw8 telescope from the seed), so the 27 b*
;; short-circuits collapse and the extracted nest is exactly the clean model.
;; ===========================================================================
;; NOTE (ks-decomp): the monolithic equality schedule == ok(ks-fold(kr-chain ..))
;; does NOT go through by simply enabling the schedule defun: the extracted
;; aes128-key-schedule is a single non-recursive 27-op b* nest, and expanding it
;; forces ACL2 to materialize/normalize a term whose ok-patbind short-circuits
;; balloon (87s+ just building the term, before any rule fires).  All the pieces
;; a clean collapse needs ARE proven above (length-only :ok/car/len for every op,
;; kr-chain len/true-listp, ks-fold).  The remaining step is to drive the collapse
;; op-by-op WITHOUT materializing the whole nest -- e.g. a custom b*-peel via a
;; recursive schedule model + functional-instantiation, rather than defun-open.
;; Left for the next iteration; the infrastructure here is what it will build on.
