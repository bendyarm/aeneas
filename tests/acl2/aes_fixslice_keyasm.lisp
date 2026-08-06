; Phase 4 -- key-schedule ASSEMBLY, part 1: the extracted schedule decomposes.
;
;   ks-decomp:  (aes::inp key) =>
;     aes128-key-schedule(100, key)
;       = (ok (ks-fold (kr-chain (seed key) 0 0)))
;
; The recursive extraction makes this tractable: the schedule body is now
; seed ; ONE recursive loop0 call ; 17 single-threaded fold at-ops -- no
; unrolled (off . rkeys) car/cdr splits at the top level.  Two layers here:
;
; (1) FUEL CANONICALIZATION.  loop0 calls key_round at fuel 99,98,...,90, but
;     every interface lemma is pinned at fuel 100.  The sub-op loop lemmas
;     (write8/ms/xc-loop0-is-*) are already fuel-generic, so we restate the
;     op-level forms at generic fuel (length-only hypotheses) and conclude
;     key-round-fuel-canon: key_round(m) = key_round(100) for m > 10 -- both
;     sides equal the same fuel-free spec form.  Downstream @100 lemmas then
;     apply verbatim inside the loop induction.
;
; (2) THE LOOP IS kr-chain.  ks-loop0-is-kr-chain: for off = 8c,
;     loop0(m, rng(c,10), rk, off) = (ok (kr-chain rk off c)) by induction on
;     the rounds remaining -- purely length-based hypotheses (the :ok of each
;     round needs only array bounds, NOT the wok invariant; wok is only needed
;     later to say what the core VALUE is).  ks-decomp then collapses the
;     schedule: seed facts + the loop lemma + the 17 fold :ok/len rewrites.
(in-package "ACL2")
(include-book "aes_fixslice_keydecomp")
(local (include-book "std/lists/nth" :dir :system))
(local (in-theory (disable len-when-wstatep true-listp-when-wstatep nth-when-zp)))

;; ---------------------------------------------------------------------------
;; (1) generic-fuel op forms (length-only), mirroring the @100 versions.
(defthm write8-is-w8spec-n
  (implies (and (natp off) (<= (+ off 8) (len rkeys)) (< (len rkeys) 4294967296)
                (<= 8 (len s)) (< 8 (nfix n)))
           (equal (aes-fixslice-encrypt-write8 n rkeys off s)
                  (ok (w8-spec 0 8 rkeys off s))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-write8)
                                  (aes-fixslice-encrypt-write8-loop0 w8-spec))
                  :use (:instance write8-loop0-is-w8spec (i 0) (e 8)))))

(defthm memshift32-is-msspec-n
  (implies (and (natp src) (<= (+ src 16) (len buffer)) (< (len buffer) 4294967296)
                (< 8 (nfix n)))
           (equal (aes-fixslice-encrypt-memshift32 n buffer src)
                  (ok (ms-spec 0 8 buffer src (+ src 8)))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-memshift32)
                                  (aes-fixslice-encrypt-memshift32-loop0 ms-spec))
                  :use (:instance ms-loop0-is-msspec (i 0) (e 8) (dst (+ src 8))))))

(defthm xor-columns-is-xcspec-n
  (implies (and (natp off) (natp dx) (<= dx off) (<= (+ off 8) (len rkeys))
                (< (len rkeys) 4294967296) (< 8 (nfix n)))
           (equal (aes-fixslice-encrypt-xor-columns n rkeys off dx dror)
                  (ok (xc-spec 0 8 rkeys off dx dror))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-xor-columns)
                                  (aes-fixslice-encrypt-xor-columns-loop0 xc-spec))
                  :use (:instance xc-loop0-is-xcspec (i 0) (e 8)))))

(defthm sub-bytes-at-form-n
  (implies (and (natp off) (<= (+ off 8) (len rk)) (< (len rk) 4294967296)
                (< 8 (nfix n)))
           (equal (aes-fixslice-encrypt-sub-bytes-at n rk off)
                  (ok (w8-spec 0 8 rk off
                        (result-ok->val (aes-fixslice-encrypt-sub-bytes (rd8 rk off)))))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-sub-bytes-at)
                                  (aes-fixslice-encrypt-sub-bytes w8-spec rd8 nth
                                   aes-fixslice-encrypt-write8)))))

(defthm sub-bytes-nots-at-form-n
  (implies (and (natp off) (<= (+ off 8) (len rk)) (< (len rk) 4294967296)
                (< 8 (nfix n)))
           (equal (aes-fixslice-encrypt-sub-bytes-nots-at n rk off)
                  (ok (w8-spec 0 8 rk off
                        (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots (rd8 rk off)))))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-sub-bytes-nots-at)
                                  (aes-fixslice-encrypt-sub-bytes-nots w8-spec rd8 nth
                                   aes-fixslice-encrypt-write8)))))

(defthm add-rc-bit-at-form-n
  (implies (and (natp off) (<= (+ off 8) (len rk)) (< (len rk) 4294967296)
                (natp bit) (< bit 8) (< 8 (nfix n)))
           (equal (aes-fixslice-encrypt-add-rc-bit-at n rk off bit)
                  (ok (w8-spec 0 8 rk off
                        (result-ok->val (aes-fixslice-encrypt-add-round-constant-bit (rd8 rk off) bit))))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-add-rc-bit-at)
                                  (aes-fixslice-encrypt-add-round-constant-bit w8-spec rd8 nth
                                   aes-fixslice-encrypt-write8)))))

;; add-rcon at generic fuel: for c < 12 both branches are chains of
;; add-rc-bit-at at bits < 8; keep the result as the nested form (fuel-free).
(defthm add-rcon-fuel-canon
  (implies (and (syntaxp (not (equal n ''100)))  ; output has fuel 100: don't re-match it
                (natp off) (<= (+ off 8) (len rk)) (< (len rk) 4294967296)
                (natp c) (< c 12) (< 8 (nfix n)))
           (equal (aes-fixslice-encrypt-add-rcon n rk off c)
                  (aes-fixslice-encrypt-add-rcon 100 rk off c)))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-add-rcon)
                                  (aes-fixslice-encrypt-add-round-constant-bit
                                   aes-fixslice-encrypt-add-rc-bit-at w8-spec rd8 nth))
           :use ((:instance add-rc-bit-at-form-n (bit c))
                 (:instance add-rc-bit-at-form-n (n 100) (bit c))))))

;; ---------------------------------------------------------------------------
;; key_round at any sufficient fuel equals key_round at 100 (length-only).
(defthm key-round-fuel-canon
  (implies (and (syntaxp (not (equal m ''100)))  ; output has fuel 100: don't re-match it
                (natp off) (<= (+ off 16) (len rk)) (< (len rk) 4294967296)
                (natp c) (< c 12) (< 10 (nfix m)))
           (equal (aes-fixslice-encrypt-key-round m rk off c)
                  (aes-fixslice-encrypt-key-round 100 rk off c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (aes-fixslice-encrypt-key-round)
                           (aes-fixslice-encrypt-memshift32 aes-fixslice-encrypt-sub-bytes-at
                            aes-fixslice-encrypt-sub-bytes-nots-at aes-fixslice-encrypt-add-rcon
                            aes-fixslice-encrypt-xor-columns aes-fixslice-encrypt-sub-bytes
                            aes-fixslice-encrypt-sub-bytes-nots
                            aes-fixslice-encrypt-add-round-constant-bit
                            w8-spec ms-spec xc-spec rd8 nth)))))

;; ---------------------------------------------------------------------------
;; (2) the recursive rcon loop IS kr-chain.  Length-only hypotheses: each
;; round's :ok needs only array bounds, so no wok/inp appears here at all --
;; the invariant is only needed later to say what the core VALUE is.
;; off = 8c keeps the offset arithmetic linear (keyexpand's lockstep trick).
(defun ks-li (m c rk off)  ; induction scheme mirroring the loop's recursion
  (declare (xargs :measure (nfix (- 10 (nfix c)))))
  (if (or (not (natp c)) (>= c 10)) (list m c rk off)
    (ks-li (1- m) (1+ c)
           (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100 rk off c)))
           (+ off 8))))

(defthm ks-loop0-is-kr-chain
  (implies (and (natp c) (<= c 10) (equal off (* 8 c)) (equal (len rk) 88)
                (natp m) (< (+ 11 (- 10 c)) m))
           (equal (aes-fixslice-encrypt-aes128-key-schedule-loop0 m (rng c 10) rk off)
                  (ok (kr-chain rk off c))))
  :hints (("Goal" :induct (ks-li m c rk off)
           :in-theory (e/d (kr-chain)
                           (aes-fixslice-encrypt-key-round key-round-unfold
                            key-round-window key-round-car key-round-len
                            key-round-frame-below rd8-of-key-round-below
                            true-listp-of-cdr-key-round result-kind-of-key-round
                            w8-spec ms-spec xc-spec rd8 nth wstatep
                            (:executable-counterpart core-ops-range-range-usize-))))
          ("Subgoal *1/2"
           :expand ((aes-fixslice-encrypt-aes128-key-schedule-loop0 m (rng c 10) rk off)
                    (kr-chain rk off c)))
          ("Subgoal *1/1"
           :expand ((aes-fixslice-encrypt-aes128-key-schedule-loop0 m (rng c 10) rk off)
                    (kr-chain rk off c)))))

;; ---------------------------------------------------------------------------
;; (3) THE DECOMPOSITION: the extracted schedule = fold over the core chain.
;; With the loop collapsed by ks-loop0-is-kr-chain, the schedule body is
;; seed ; (ok core) ; 17 single-threaded fold at-ops.  The theory is pinned to
;; ground-zero + exactly the needed rewrites: the 20-deep ok-binder if-nest
;; otherwise sends the default theory's preprocessor into an exponential
;; clause split (390s+ of clausification with 0.05s of actual proving).
;; (result-kind (ok x)) = :ok, proved here in the full theory so the pinned
;; ks-decomp theory below can use the single rune without opening the tagsum.
(defthm rk-of-ok (equal (result-kind (result-ok x)) :ok))

;; ---------------------------------------------------------------------------
;; IN PROGRESS -- ks-decomp, the final collapse:
;;   (aes::inp key) => schedule(100,key) = (ok (ks-fold (kr-chain (seed key) 0 0)))
;; Status: the pinned-theory collapse now traverses the whole schedule body and
;; ks-loop0-is-kr-chain fires (the loop becomes (ok (kr-chain seed 0 0))); the
;; run was killed at the wall-clock limit with three residual subgoals -- the
;; final ok-binder/constructor bookkeeping (rk-of-ok / ok-elim were not yet
;; engaging; likely the (eq (result-kind ..) :ok) binder tests want eq handled
;; alongside the helpers).  The helpers (result-p-of-sbn-at, ok-elim) are
;; certified above.  Kept disabled so the book certifies; next session resumes
;; here -- or the fold section gets re-rolled at the source like the rcon loop,
;; which shrinks the schedule body to ~6 binds and makes this collapse trivial.
#|
(defthm ks-decomp
  (implies (aes::inp key)
           (equal (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key))
                  (ks-fold (kr-chain (result-ok->val
                                 (aes-fixslice-encrypt-bitslice-into 100 (array-repeat 88 0) 0 key key))
                               0 0))))
  :hints (("Goal" :do-not-induct t :do-not '(preprocess)
           :in-theory (union-theories (theory 'ground-zero)
                        '((:definition aes-fixslice-encrypt-aes128-key-schedule)
                          (:definition ks-fold)
                          (:definition core-iter-traits-collect-impl-core-iter-traits-collect-intoiterator-for-core-ops-range-range-usize-into-iter-core-ops-range-range-usize-)
                          (:definition not)
                          (:rewrite len-of-array-repeat)
                          (:rewrite result-kind-of-seed) (:rewrite len-of-seed) (:rewrite len-of-core)
                          (:rewrite result-kind-of-isr1-at-len) (:rewrite len-of-isr1-at-len)
                          (:rewrite result-kind-of-isr2-at-len) (:rewrite len-of-isr2-at-len)
                          (:rewrite result-kind-of-isr3-at-len) (:rewrite len-of-isr3-at-len)
                          (:rewrite result-kind-of-sbn-at-len) (:rewrite len-of-sbn-at-len)
                          (:rewrite result-ok->val-of-result-ok)
                          (:rewrite rk-of-ok) (:rewrite ks-loop0-is-kr-chain)
                          (:executable-counterpart nfix) (:executable-counterpart zp)
                          (:executable-counterpart binary-+) (:executable-counterpart binary-*)
                          (:executable-counterpart <) (:executable-counterpart unary--)
                          (:executable-counterpart natp) (:executable-counterpart integerp)
                          (:executable-counterpart equal) (:executable-counterpart eq))))))

(defthm ks-decomp-ok
  (implies (aes::inp key)
           (equal (result-kind (aes-fixslice-encrypt-aes128-key-schedule 100 key)) :ok))
  :hints (("Goal" :do-not-induct t :do-not '(preprocess)
           :in-theory (union-theories (theory 'ground-zero)
                        '((:definition aes-fixslice-encrypt-aes128-key-schedule)
                          (:definition ks-fold)
                          (:definition core-iter-traits-collect-impl-core-iter-traits-collect-intoiterator-for-core-ops-range-range-usize-into-iter-core-ops-range-range-usize-)
                          (:definition not)
                          (:rewrite len-of-array-repeat)
                          (:rewrite result-kind-of-seed) (:rewrite len-of-seed) (:rewrite len-of-core)
                          (:rewrite result-kind-of-isr1-at-len) (:rewrite len-of-isr1-at-len)
                          (:rewrite result-kind-of-isr2-at-len) (:rewrite len-of-isr2-at-len)
                          (:rewrite result-kind-of-isr3-at-len) (:rewrite len-of-isr3-at-len)
                          (:rewrite result-kind-of-sbn-at-len) (:rewrite len-of-sbn-at-len)
                          (:rewrite result-ok->val-of-result-ok)
                          (:rewrite rk-of-ok) (:rewrite ks-loop0-is-kr-chain)
                          (:executable-counterpart nfix) (:executable-counterpart zp)
                          (:executable-counterpart binary-+) (:executable-counterpart binary-*)
                          (:executable-counterpart <) (:executable-counterpart unary--)
                          (:executable-counterpart natp) (:executable-counterpart integerp)
                          (:executable-counterpart equal) (:executable-counterpart eq))))))


|#
