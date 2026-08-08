
;; ===========================================================================
;; (C3) enc-model: the 33-op body collapses onto a pure value chain.
;; enc-chain rounds: ark0 | 9 x [sub_bytes ; mix_columns_c ; ark(8r)] with
;; c = r mod 4 | shift_rows_2 ; sub_bytes ; ark80.  inv_bitslice stays outside.
;; A single shape predicate.  The C2 rules carry (true-listp s) AND
;; (equal (len s) 8) as separate hyps; relieving both at chain depth k
;; re-descends the whole nest per hyp -- a 2^k relief tree (measured: ~x5
;; per layer).  One predicate with one closure rule per op makes each
;; descent linear, so the 33-op collapse is O(k^2) overall.
(defund st8p (s) (and (true-listp s) (equal (len s) 8)))
(local (defthm st8p-open
  (implies (st8p s) (and (true-listp s) (equal (len s) 8)))
  :hints (("Goal" :in-theory (enable st8p)))))
(defthm st8p-of-bitslice
  (implies (and (aes::inp b0) (aes::inp b1))
           (st8p (result-ok->val (aes-fixslice-encrypt-bitslice b0 b1))))
  :hints (("Goal" :in-theory (e/d (st8p) (aes-fixslice-encrypt-bitslice))
           :use (:instance wstatep-of-bitslice))))
(defthm st8p-of-arkw-spec
  (implies (st8p s) (st8p (arkw-spec 0 8 s rk off)))
  :hints (("Goal" :in-theory (e/d (st8p) (arkw-spec u32-xor nth)))))
(defthm st8p-of-sb
  (implies (st8p s) (st8p (result-ok->val (aes-fixslice-encrypt-sub-bytes s))))
  :hints (("Goal" :in-theory (e/d (st8p) (aes-fixslice-encrypt-sub-bytes)))))
(defthm rk-of-sb-st
  (implies (st8p s) (equal (result-kind (aes-fixslice-encrypt-sub-bytes s)) :ok))
  :hints (("Goal" :in-theory (e/d (st8p) (aes-fixslice-encrypt-sub-bytes)))))
(defthm st8p-of-mc0
  (implies (st8p s) (st8p (result-ok->val (aes-fixslice-encrypt-mix-columns-0 s))))
  :hints (("Goal" :in-theory (e/d (st8p) (aes-fixslice-encrypt-mix-columns-0)))))
(defthm rk-of-mc0-st
  (implies (st8p s) (equal (result-kind (aes-fixslice-encrypt-mix-columns-0 s)) :ok))
  :hints (("Goal" :in-theory (e/d (st8p) (aes-fixslice-encrypt-mix-columns-0)))))
(defthm st8p-of-mc1
  (implies (st8p s) (st8p (result-ok->val (aes-fixslice-encrypt-mix-columns-1 s))))
  :hints (("Goal" :in-theory (e/d (st8p) (aes-fixslice-encrypt-mix-columns-1)))))
(defthm rk-of-mc1-st
  (implies (st8p s) (equal (result-kind (aes-fixslice-encrypt-mix-columns-1 s)) :ok))
  :hints (("Goal" :in-theory (e/d (st8p) (aes-fixslice-encrypt-mix-columns-1)))))
(defthm st8p-of-mc2
  (implies (st8p s) (st8p (result-ok->val (aes-fixslice-encrypt-mix-columns-2 s))))
  :hints (("Goal" :in-theory (e/d (st8p) (aes-fixslice-encrypt-mix-columns-2)))))
(defthm rk-of-mc2-st
  (implies (st8p s) (equal (result-kind (aes-fixslice-encrypt-mix-columns-2 s)) :ok))
  :hints (("Goal" :in-theory (e/d (st8p) (aes-fixslice-encrypt-mix-columns-2)))))
(defthm st8p-of-mc3
  (implies (st8p s) (st8p (result-ok->val (aes-fixslice-encrypt-mix-columns-3 s))))
  :hints (("Goal" :in-theory (e/d (st8p) (aes-fixslice-encrypt-mix-columns-3)))))
(defthm rk-of-mc3-st
  (implies (st8p s) (equal (result-kind (aes-fixslice-encrypt-mix-columns-3 s)) :ok))
  :hints (("Goal" :in-theory (e/d (st8p) (aes-fixslice-encrypt-mix-columns-3)))))
(defthm st8p-of-sr2
  (implies (st8p s) (st8p (result-ok->val (aes-fixslice-encrypt-shift-rows-2 100 s))))
  :hints (("Goal" :in-theory (e/d (st8p) (aes-fixslice-encrypt-shift-rows-2)))))
(defthm rk-of-sr2-st
  (implies (st8p s) (equal (result-kind (aes-fixslice-encrypt-shift-rows-2 100 s)) :ok))
  :hints (("Goal" :in-theory (e/d (st8p) (aes-fixslice-encrypt-shift-rows-2)))))
(defthm ark-form100-st
  (implies (and (st8p s) (true-listp rk) (equal (len rk) 88) (natp off) (<= (+ off 8) 88))
           (equal (aes-fixslice-encrypt-add-round-key 100 s rk off)
                  (ok (arkw-spec 0 8 s rk off))))
  :hints (("Goal" :in-theory (e/d (st8p) (aes-fixslice-encrypt-add-round-key arkw-spec))
           :use ark-form100)))

(defund enc-chain (rk s)
  (b* ((s (arkw-spec 0 8 s rk 0))
       (s (arkw-spec 0 8 (result-ok->val (aes-fixslice-encrypt-mix-columns-1 (result-ok->val (aes-fixslice-encrypt-sub-bytes s)))) rk 8))
       (s (arkw-spec 0 8 (result-ok->val (aes-fixslice-encrypt-mix-columns-2 (result-ok->val (aes-fixslice-encrypt-sub-bytes s)))) rk 16))
       (s (arkw-spec 0 8 (result-ok->val (aes-fixslice-encrypt-mix-columns-3 (result-ok->val (aes-fixslice-encrypt-sub-bytes s)))) rk 24))
       (s (arkw-spec 0 8 (result-ok->val (aes-fixslice-encrypt-mix-columns-0 (result-ok->val (aes-fixslice-encrypt-sub-bytes s)))) rk 32))
       (s (arkw-spec 0 8 (result-ok->val (aes-fixslice-encrypt-mix-columns-1 (result-ok->val (aes-fixslice-encrypt-sub-bytes s)))) rk 40))
       (s (arkw-spec 0 8 (result-ok->val (aes-fixslice-encrypt-mix-columns-2 (result-ok->val (aes-fixslice-encrypt-sub-bytes s)))) rk 48))
       (s (arkw-spec 0 8 (result-ok->val (aes-fixslice-encrypt-mix-columns-3 (result-ok->val (aes-fixslice-encrypt-sub-bytes s)))) rk 56))
       (s (arkw-spec 0 8 (result-ok->val (aes-fixslice-encrypt-mix-columns-0 (result-ok->val (aes-fixslice-encrypt-sub-bytes s)))) rk 64))
       (s (arkw-spec 0 8 (result-ok->val (aes-fixslice-encrypt-mix-columns-1 (result-ok->val (aes-fixslice-encrypt-sub-bytes s)))) rk 72))
       (s (arkw-spec 0 8 (result-ok->val (aes-fixslice-encrypt-sub-bytes (result-ok->val (aes-fixslice-encrypt-shift-rows-2 100 s)))) rk 80)))
    s))

(defthm enc-collapse
  (implies (and (aes::inp b0) (aes::inp b1)
                (true-listp rk) (equal (len rk) 88))
           (equal (aes-fixslice-encrypt-aes128-encrypt 100 rk b0 b1)
                  (aes-fixslice-encrypt-inv-bitslice
                    (enc-chain rk (result-ok->val (aes-fixslice-encrypt-bitslice b0 b1))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'ground-zero)
                        '((:definition aes-fixslice-encrypt-aes128-encrypt)
                          (:definition enc-chain)
                          (:definition not)
                          (:rewrite bitslice-ok) (:rewrite st8p-of-bitslice)
                          (:rewrite st8p-of-arkw-spec) (:rewrite st8p-of-sb)
                          (:rewrite st8p-of-mc0) (:rewrite st8p-of-mc1)
                          (:rewrite st8p-of-mc2) (:rewrite st8p-of-mc3)
                          (:rewrite st8p-of-sr2)
                          (:rewrite rk-of-sb-st)
                          (:rewrite rk-of-mc0-st) (:rewrite rk-of-mc1-st)
                          (:rewrite rk-of-mc2-st) (:rewrite rk-of-mc3-st)
                          (:rewrite rk-of-sr2-st)
                          (:rewrite ark-form100-st)
                          (:rewrite result-ok->val-of-result-ok)
                          (:rewrite rk-of-ok2)
                          (:executable-counterpart nfix) (:executable-counterpart zp)
                          (:executable-counterpart binary-+) (:executable-counterpart binary-*)
                          (:executable-counterpart <) (:executable-counterpart unary--)
                          (:executable-counterpart natp) (:executable-counterpart integerp)
                          (:executable-counterpart equal) (:executable-counterpart eq))))))

(defthm st8p-of-enc-chain
  (implies (and (st8p s) (true-listp rk) (equal (len rk) 88))
           (st8p (enc-chain rk s)))
  :hints (("Goal" :in-theory (e/d (enc-chain)
                    (arkw-spec u32-xor nth st8p
                     aes-fixslice-encrypt-sub-bytes
                     aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1
                     aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3
                     aes-fixslice-encrypt-shift-rows-2)))))
(defthm result-kind-of-encrypt
  (implies (and (aes::inp b0) (aes::inp b1) (true-listp rk) (equal (len rk) 88))
           (equal (result-kind (aes-fixslice-encrypt-aes128-encrypt 100 rk b0 b1)) :ok))
  :hints (("Goal" :in-theory (e/d () (aes-fixslice-encrypt-aes128-encrypt
                                      aes-fixslice-encrypt-inv-bitslice enc-chain
                                      aes-fixslice-encrypt-bitslice st8p))
           :use (enc-collapse
                 (:instance st8p-of-enc-chain (s (result-ok->val (aes-fixslice-encrypt-bitslice b0 b1))))
                 (:instance st8p-open (s (enc-chain rk (result-ok->val (aes-fixslice-encrypt-bitslice b0 b1)))))
                 (:instance result-kind-of-inv-bitslice-len
                   (s (enc-chain rk (result-ok->val (aes-fixslice-encrypt-bitslice b0 b1)))))))))
