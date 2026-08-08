
;; ===========================================================================
;; (C2) length-only :ok / len / true-listp for the remaining cipher ops.
;; All by the explicit-8 template: prove on an explicit 8-list (everything
;; computes; no shape splits), lift via expand-len-8.

(local (defthm rk-mc0-explicit
  (equal (result-kind (aes-fixslice-encrypt-mix-columns-0 (list a0 a1 a2 a3 a4 a5 a6 a7))) :ok)
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-mix-columns-0) (u32-xor u32-and u32-or))))))
(local (defthm len-mc0-explicit
  (equal (len (result-ok->val (aes-fixslice-encrypt-mix-columns-0 (list a0 a1 a2 a3 a4 a5 a6 a7)))) 8)
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-mix-columns-0) (u32-xor u32-and u32-or))))))
(local (defthm tl-mc0-explicit
  (true-listp (result-ok->val (aes-fixslice-encrypt-mix-columns-0 (list a0 a1 a2 a3 a4 a5 a6 a7))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-mix-columns-0) (u32-xor u32-and u32-or))))))
(defthm result-kind-of-mc0-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (result-kind (aes-fixslice-encrypt-mix-columns-0 s)) :ok))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-mix-columns-0 nth)
           :use ((:instance rk-mc0-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))
(defthm len-of-mc0-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (len (result-ok->val (aes-fixslice-encrypt-mix-columns-0 s))) 8))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-mix-columns-0 nth)
           :use ((:instance len-mc0-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))
(defthm true-listp-of-mc0-len
  (implies (and (true-listp s) (equal (len s) 8))
           (true-listp (result-ok->val (aes-fixslice-encrypt-mix-columns-0 s))))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-mix-columns-0 nth)
           :use ((:instance tl-mc0-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))

(local (defthm rk-mc1-explicit
  (equal (result-kind (aes-fixslice-encrypt-mix-columns-1 (list a0 a1 a2 a3 a4 a5 a6 a7))) :ok)
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-mix-columns-1) (u32-xor u32-and u32-or))))))
(local (defthm len-mc1-explicit
  (equal (len (result-ok->val (aes-fixslice-encrypt-mix-columns-1 (list a0 a1 a2 a3 a4 a5 a6 a7)))) 8)
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-mix-columns-1) (u32-xor u32-and u32-or))))))
(local (defthm tl-mc1-explicit
  (true-listp (result-ok->val (aes-fixslice-encrypt-mix-columns-1 (list a0 a1 a2 a3 a4 a5 a6 a7))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-mix-columns-1) (u32-xor u32-and u32-or))))))
(defthm result-kind-of-mc1-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (result-kind (aes-fixslice-encrypt-mix-columns-1 s)) :ok))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-mix-columns-1 nth)
           :use ((:instance rk-mc1-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))
(defthm len-of-mc1-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (len (result-ok->val (aes-fixslice-encrypt-mix-columns-1 s))) 8))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-mix-columns-1 nth)
           :use ((:instance len-mc1-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))
(defthm true-listp-of-mc1-len
  (implies (and (true-listp s) (equal (len s) 8))
           (true-listp (result-ok->val (aes-fixslice-encrypt-mix-columns-1 s))))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-mix-columns-1 nth)
           :use ((:instance tl-mc1-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))

(local (defthm rk-mc2-explicit
  (equal (result-kind (aes-fixslice-encrypt-mix-columns-2 (list a0 a1 a2 a3 a4 a5 a6 a7))) :ok)
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-mix-columns-2) (u32-xor u32-and u32-or))))))
(local (defthm len-mc2-explicit
  (equal (len (result-ok->val (aes-fixslice-encrypt-mix-columns-2 (list a0 a1 a2 a3 a4 a5 a6 a7)))) 8)
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-mix-columns-2) (u32-xor u32-and u32-or))))))
(local (defthm tl-mc2-explicit
  (true-listp (result-ok->val (aes-fixslice-encrypt-mix-columns-2 (list a0 a1 a2 a3 a4 a5 a6 a7))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-mix-columns-2) (u32-xor u32-and u32-or))))))
(defthm result-kind-of-mc2-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (result-kind (aes-fixslice-encrypt-mix-columns-2 s)) :ok))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-mix-columns-2 nth)
           :use ((:instance rk-mc2-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))
(defthm len-of-mc2-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (len (result-ok->val (aes-fixslice-encrypt-mix-columns-2 s))) 8))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-mix-columns-2 nth)
           :use ((:instance len-mc2-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))
(defthm true-listp-of-mc2-len
  (implies (and (true-listp s) (equal (len s) 8))
           (true-listp (result-ok->val (aes-fixslice-encrypt-mix-columns-2 s))))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-mix-columns-2 nth)
           :use ((:instance tl-mc2-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))

(local (defthm rk-mc3-explicit
  (equal (result-kind (aes-fixslice-encrypt-mix-columns-3 (list a0 a1 a2 a3 a4 a5 a6 a7))) :ok)
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-mix-columns-3) (u32-xor u32-and u32-or))))))
(local (defthm len-mc3-explicit
  (equal (len (result-ok->val (aes-fixslice-encrypt-mix-columns-3 (list a0 a1 a2 a3 a4 a5 a6 a7)))) 8)
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-mix-columns-3) (u32-xor u32-and u32-or))))))
(local (defthm tl-mc3-explicit
  (true-listp (result-ok->val (aes-fixslice-encrypt-mix-columns-3 (list a0 a1 a2 a3 a4 a5 a6 a7))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-mix-columns-3) (u32-xor u32-and u32-or))))))
(defthm result-kind-of-mc3-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (result-kind (aes-fixslice-encrypt-mix-columns-3 s)) :ok))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-mix-columns-3 nth)
           :use ((:instance rk-mc3-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))
(defthm len-of-mc3-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (len (result-ok->val (aes-fixslice-encrypt-mix-columns-3 s))) 8))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-mix-columns-3 nth)
           :use ((:instance len-mc3-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))
(defthm true-listp-of-mc3-len
  (implies (and (true-listp s) (equal (len s) 8))
           (true-listp (result-ok->val (aes-fixslice-encrypt-mix-columns-3 s))))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-mix-columns-3 nth)
           :use ((:instance tl-mc3-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))

;; inv_bitslice plumbing: delta_swap_2 / shr / u8-cast are :ok for the
;; constant shifts and 255-masks that appear, so the ops stay opaque.
(local (defthm rk-of-ds2
  (implies (< (nfix shift) 32)
           (equal (result-kind (aes-fixslice-encrypt-delta-swap-2 a b shift mask)) :ok))
  :hints (("Goal" :in-theory (enable aes-fixslice-encrypt-delta-swap-2)))))
(local (defthm rk-of-u32-shr-lt
  (implies (< (nfix n) 32)
           (equal (result-kind (u32-shr x n)) :ok))))
(local (defthm u8p-of-u32-and-255
  (u8p (u32-and x 255))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-logand (n 8) (i x) (j 255))
           :in-theory (e/d (unsigned-byte-p) (unsigned-byte-p-of-logand))))))
(local (defthm rk-invb-explicit
  (equal (result-kind (aes-fixslice-encrypt-inv-bitslice (list a0 a1 a2 a3 a4 a5 a6 a7))) :ok)
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-bitslice)
                                  (u32-xor u32-and u32-or u32-shl u32-shr u8-cast
                                   aes-fixslice-encrypt-delta-swap-2))))))
(local (defthm rp-invb-explicit
  (result-p (aes-fixslice-encrypt-inv-bitslice (list a0 a1 a2 a3 a4 a5 a6 a7)))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-bitslice)
                                  (u32-xor u32-and u32-or u32-shl u32-shr u8-cast
                                   aes-fixslice-encrypt-delta-swap-2))))))
(defthm result-kind-of-inv-bitslice-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (result-kind (aes-fixslice-encrypt-inv-bitslice s)) :ok))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-inv-bitslice nth)
           :use ((:instance rk-invb-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))
(defthm result-p-of-inv-bitslice
  (implies (and (true-listp s) (equal (len s) 8))
           (result-p (aes-fixslice-encrypt-inv-bitslice s)))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-inv-bitslice nth)
           :use ((:instance rp-invb-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))
;; sub_bytes true-listp (rk/len already in keydecomp).
(local (defthm tl-sb-explicit
  (true-listp (result-ok->val (aes-fixslice-encrypt-sub-bytes (list a0 a1 a2 a3 a4 a5 a6 a7))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-sub-bytes) (u32-xor u32-and))))))
(defthm true-listp-of-sub-bytes-len
  (implies (and (true-listp s) (equal (len s) 8))
           (true-listp (result-ok->val (aes-fixslice-encrypt-sub-bytes s))))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-sub-bytes nth)
           :use ((:instance tl-sb-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))
;; shift_rows_2 direct forms (the isr2 lemmas are about the alias fn).
(defthm result-kind-of-sr2-100
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (result-kind (aes-fixslice-encrypt-shift-rows-2 100 s)) :ok))
  :hints (("Goal" :use result-kind-of-isr2-len
           :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-2) (aes-fixslice-encrypt-shift-rows-2)))))
(defthm len-of-sr2-100-d
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (len (result-ok->val (aes-fixslice-encrypt-shift-rows-2 100 s))) 8))
  :hints (("Goal" :use len-of-isr2-len
           :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-2) (aes-fixslice-encrypt-shift-rows-2)))))
(defthm true-listp-of-sr2-100-d
  (implies (and (true-listp s) (equal (len s) 8))
           (true-listp (result-ok->val (aes-fixslice-encrypt-shift-rows-2 100 s))))
  :hints (("Goal" :use true-listp-of-isr2-100
           :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-2) (aes-fixslice-encrypt-shift-rows-2)))))

;; add_round_key value/shape at fuel 100 via the loop spec.
(defthm len-of-arkw-spec
  (implies (and (natp i) (natp e) (<= e (len s)))
           (equal (len (arkw-spec i e s rk off)) (len s)))
  :hints (("Goal" :induct (arkw-spec i e s rk off)
           :in-theory (e/d () (u32-xor nth)))))
(defthm true-listp-of-arkw-spec
  (implies (true-listp s) (true-listp (arkw-spec i e s rk off)))
  :hints (("Goal" :induct (arkw-spec i e s rk off)
           :in-theory (e/d () (u32-xor nth)))))
(defthm ark-form100
  (implies (and (natp off) (<= (+ off 8) (len rk)) (< (len rk) 4294967296)
                (<= 8 (len s)))
           (equal (aes-fixslice-encrypt-add-round-key 100 s rk off)
                  (ok (arkw-spec 0 8 s rk off))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-add-round-key)
                                  (aes-fixslice-encrypt-add-round-key-loop0 u32-xor nth))
           :use (:instance ark-loop0-is-spec (i 0) (e 8) (n 100)))))
