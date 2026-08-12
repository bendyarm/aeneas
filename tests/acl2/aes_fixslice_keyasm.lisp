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
  (implies (and (natp src) (equal (rem src 8) 0)
                (<= (+ src 16) (len buffer)) (< (len buffer) 4294967296)
                (true-listp buffer) (< 8 (nfix n)))
           (equal (aes-fixslice-encrypt-memshift32 n buffer src)
                  (ok (ms-spec 0 8 buffer src (+ src 8)))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-memshift32)
                                  (aes-fixslice-encrypt-memshift32-loop0 ms-spec ms-spec-d
                                   rev-on-range))
                  :use ((:instance ms-loop0-is-msspec-d (s 0) (e 8) (dst (+ src 8)))
                        (:instance ms-spec-d-is-ms-spec (e 8) (dst (+ src 8)))))))

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
                (natp off) (equal (rem off 8) 0)
                (<= (+ off 16) (len rk)) (< (len rk) 4294967296)
                (true-listp rk) (natp c) (< c 12) (< 10 (nfix m)))
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
                (true-listp rk) (natp m) (< (+ 11 (- 10 c)) m))
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


;; ===========================================================================
;; (3) The FOLD loops (recursive extraction of the fold section).
;; loop1 = the (8..72).step_by(32)-equivalent isr triple at base 8+32k, k<2;
;; loop2 = the NOTs loop, sub_bytes_nots_at(8i) for i in 1..11.
;; Same recipe as the rcon loop: fuel-canonicalize each at-op, then collapse
;; the loop to a spec chain (loop1 by explicit 2-step expansion; loop2 by
;; induction).
;; ===========================================================================
;; ---- shift-rows loops are fuel-irrelevant (value-level): two-fuel equality
;; by SIMULTANEOUS induction on both fuels (an IH at one decremented fuel
;; cannot reach the other side), gates kept closed; then the isr ops
;; canonicalize to fuel 100.
(defun sr3-ind2 (n1 n2 i e s)
  (declare (xargs :measure (nfix (- (nfix e) (nfix i)))))
  (if (and (natp i) (natp e) (< i e) (not (zp n1)) (not (zp n2)) (< i (len s)))
      (sr3-ind2 (1- n1) (1- n2) (+ i 1) e (update-nth i (result-ok->val (aes-fixslice-encrypt-delta-swap-1 (result-ok->val (aes-fixslice-encrypt-delta-swap-1 (nth i s) 4 51317760)) 2 855651072)) s))
    (list n1 n2 i e s)))
(defthm sr3-loop0-two-fuel
  (implies (and (natp i) (natp e) (<= i e) (< (len s) 4294967296) (<= e (len s))
                (< (- e i) (nfix n1)) (< (- e i) (nfix n2)))
           (equal (aes-fixslice-encrypt-shift-rows-3-loop0 n1 (rng i e) s)
                  (aes-fixslice-encrypt-shift-rows-3-loop0 n2 (rng i e) s)))
  :rule-classes nil
  :hints (("Goal" :induct (sr3-ind2 n1 n2 i e s)
           :in-theory (disable aes-fixslice-encrypt-shift-rows-3-loop0
                               aes-fixslice-encrypt-delta-swap-1
                               (:executable-counterpart aes-fixslice-encrypt-delta-swap-1)
                               u32-xor u32-and u32-shl u32-shr nth
                               (:executable-counterpart core-ops-range-range-usize-)))))
(defun sr2-ind2 (n1 n2 i e s)
  (declare (xargs :measure (nfix (- (nfix e) (nfix i)))))
  (if (and (natp i) (natp e) (< i e) (not (zp n1)) (not (zp n2)) (< i (len s)))
      (sr2-ind2 (1- n1) (1- n2) (+ i 1) e (update-nth i (result-ok->val (aes-fixslice-encrypt-delta-swap-1 (nth i s) 4 251662080)) s))
    (list n1 n2 i e s)))
(defthm sr2-loop0-two-fuel
  (implies (and (natp i) (natp e) (<= i e) (< (len s) 4294967296) (<= e (len s))
                (< (- e i) (nfix n1)) (< (- e i) (nfix n2)))
           (equal (aes-fixslice-encrypt-shift-rows-2-loop0 n1 (rng i e) s)
                  (aes-fixslice-encrypt-shift-rows-2-loop0 n2 (rng i e) s)))
  :rule-classes nil
  :hints (("Goal" :induct (sr2-ind2 n1 n2 i e s)
           :in-theory (disable aes-fixslice-encrypt-shift-rows-2-loop0
                               aes-fixslice-encrypt-delta-swap-1
                               (:executable-counterpart aes-fixslice-encrypt-delta-swap-1)
                               u32-xor u32-and u32-shl u32-shr nth
                               (:executable-counterpart core-ops-range-range-usize-)))))
(defun sr1-ind2 (n1 n2 i e s)
  (declare (xargs :measure (nfix (- (nfix e) (nfix i)))))
  (if (and (natp i) (natp e) (< i e) (not (zp n1)) (not (zp n2)) (< i (len s)))
      (sr1-ind2 (1- n1) (1- n2) (+ i 1) e (update-nth i (result-ok->val (aes-fixslice-encrypt-delta-swap-1 (result-ok->val (aes-fixslice-encrypt-delta-swap-1 (nth i s) 4 202310400)) 2 855651072)) s))
    (list n1 n2 i e s)))
(defthm sr1-loop0-two-fuel
  (implies (and (natp i) (natp e) (<= i e) (< (len s) 4294967296) (<= e (len s))
                (< (- e i) (nfix n1)) (< (- e i) (nfix n2)))
           (equal (aes-fixslice-encrypt-shift-rows-1-loop0 n1 (rng i e) s)
                  (aes-fixslice-encrypt-shift-rows-1-loop0 n2 (rng i e) s)))
  :rule-classes nil
  :hints (("Goal" :induct (sr1-ind2 n1 n2 i e s)
           :in-theory (disable aes-fixslice-encrypt-shift-rows-1-loop0
                               aes-fixslice-encrypt-delta-swap-1
                               (:executable-counterpart aes-fixslice-encrypt-delta-swap-1)
                               u32-xor u32-and u32-shl u32-shr nth
                               (:executable-counterpart core-ops-range-range-usize-)))))
(defthm isr1-fuel-canon
  (implies (and (syntaxp (not (equal n (quote (quote 100)))))
                (true-listp s) (equal (len s) 8) (< 8 (nfix n)))
           (equal (aes-fixslice-encrypt-inv-shift-rows-1 n s)
                  (aes-fixslice-encrypt-inv-shift-rows-1 100 s)))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-1 aes-fixslice-encrypt-shift-rows-3)
                                  (aes-fixslice-encrypt-shift-rows-3-loop0))
           :use ((:instance sr3-loop0-two-fuel (i 0) (e 8) (n1 n) (n2 100))))))
(defthm isr2-fuel-canon
  (implies (and (syntaxp (not (equal n (quote (quote 100)))))
                (true-listp s) (equal (len s) 8) (< 8 (nfix n)))
           (equal (aes-fixslice-encrypt-inv-shift-rows-2 n s)
                  (aes-fixslice-encrypt-inv-shift-rows-2 100 s)))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-2 aes-fixslice-encrypt-shift-rows-2)
                                  (aes-fixslice-encrypt-shift-rows-2-loop0))
           :use ((:instance sr2-loop0-two-fuel (i 0) (e 8) (n1 n) (n2 100))))))
(defthm isr3-fuel-canon
  (implies (and (syntaxp (not (equal n (quote (quote 100)))))
                (true-listp s) (equal (len s) 8) (< 8 (nfix n)))
           (equal (aes-fixslice-encrypt-inv-shift-rows-3 n s)
                  (aes-fixslice-encrypt-inv-shift-rows-3 100 s)))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-3 aes-fixslice-encrypt-shift-rows-1)
                                  (aes-fixslice-encrypt-shift-rows-1-loop0))
           :use ((:instance sr1-loop0-two-fuel (i 0) (e 8) (n1 n) (n2 100))))))
;; at-level canonicalization (length-only): open the -at, canonicalize the op
;; inside (rd8 windows are always len-8 true-lists), keep write8 via the
;; generic w8spec form on both sides.
(defthm isr1-at-fuel-canon
  (implies (and (syntaxp (not (equal m ''100)))
                (natp off) (<= (+ off 8) (len rk)) (< (len rk) 4294967296) (< 8 (nfix m)))
           (equal (aes-fixslice-encrypt-inv-shift-rows-1-at m rk off)
                  (aes-fixslice-encrypt-inv-shift-rows-1-at 100 rk off)))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-1-at)
                                  (aes-fixslice-encrypt-inv-shift-rows-1 w8-spec rd8 nth
                                   aes-fixslice-encrypt-write8)))))
(defthm isr2-at-fuel-canon
  (implies (and (syntaxp (not (equal m ''100)))
                (natp off) (<= (+ off 8) (len rk)) (< (len rk) 4294967296) (< 8 (nfix m)))
           (equal (aes-fixslice-encrypt-inv-shift-rows-2-at m rk off)
                  (aes-fixslice-encrypt-inv-shift-rows-2-at 100 rk off)))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-2-at)
                                  (aes-fixslice-encrypt-inv-shift-rows-2 w8-spec rd8 nth
                                   aes-fixslice-encrypt-write8)))))
(defthm isr3-at-fuel-canon
  (implies (and (syntaxp (not (equal m ''100)))
                (natp off) (<= (+ off 8) (len rk)) (< (len rk) 4294967296) (< 8 (nfix m)))
           (equal (aes-fixslice-encrypt-inv-shift-rows-3-at m rk off)
                  (aes-fixslice-encrypt-inv-shift-rows-3-at 100 rk off)))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-3-at)
                                  (aes-fixslice-encrypt-inv-shift-rows-3 w8-spec rd8 nth
                                   aes-fixslice-encrypt-write8)))))
(defthm sbn-at-fuel-canon
  (implies (and (syntaxp (not (equal m ''100)))
                (natp off) (<= (+ off 8) (len rk)) (< (len rk) 4294967296) (< 8 (nfix m)))
           (equal (aes-fixslice-encrypt-sub-bytes-nots-at m rk off)
                  (aes-fixslice-encrypt-sub-bytes-nots-at 100 rk off)))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-sub-bytes-nots-at)
                                  (aes-fixslice-encrypt-sub-bytes-nots w8-spec rd8 nth
                                   aes-fixslice-encrypt-write8)))))

;; ---------------------------------------------------------------------------
;; the spec chains (all at-ops at canonical fuel 100, kept opaque).
(defund isr-step (rk base)
  (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-3-at 100
    (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-2-at 100
      (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1-at 100 rk base))
      (+ base 8)))
    (+ base 16))))

;; the NOTs chain, threading the byte offset additively (off = 8i, lockstep).
(defun sbn-chain (rk off i)
  (declare (xargs :measure (nfix (- 11 (nfix i)))))
  (if (or (not (natp i)) (>= i 11)) rk
    (sbn-chain (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots-at 100 rk off))
               (+ off 8) (1+ i))))

;; length facts for the chains (thread the @100 len lemmas).
(defthm len-of-isr-step
  (implies (and (natp base) (<= (+ base 24) (len rk)) (< (len rk) 4294967296))
           (equal (len (isr-step rk base)) (len rk)))
  :hints (("Goal" :in-theory (e/d (isr-step)
                                  (aes-fixslice-encrypt-inv-shift-rows-1-at
                                   aes-fixslice-encrypt-inv-shift-rows-2-at
                                   aes-fixslice-encrypt-inv-shift-rows-3-at)))))

(defthm mul-8-le-80 (implies (and (natp i) (< i 11)) (<= (* 8 i) 80)))

(defthm len-of-sbn-chain
  (implies (and (equal (len rk) 88) (natp i) (<= 1 i) (equal off (* 8 i)))
           (equal (len (sbn-chain rk off i)) 88))
  :hints (("Goal" :induct (sbn-chain rk off i)
           :in-theory (e/d (sbn-chain) (aes-fixslice-encrypt-sub-bytes-nots-at nth)))))

;; ---------------------------------------------------------------------------
;; loop1 (isr triples at k = 0, 1) collapses by explicit two-step expansion.
(defthm ks-loop1-collapse
  (implies (and (equal (len rk) 88) (natp m) (< 12 (nfix m)))
           (equal (aes-fixslice-encrypt-aes128-key-schedule-loop1 m (rng 0 2) rk)
                  (ok (isr-step (isr-step rk 8) 40))))
  :hints (("Goal" :do-not-induct t
           :expand ((aes-fixslice-encrypt-aes128-key-schedule-loop1 m (rng 0 2) rk)
                    (:free (mm rr) (aes-fixslice-encrypt-aes128-key-schedule-loop1 mm (rng 1 2) rr))
                    (:free (mm rr) (aes-fixslice-encrypt-aes128-key-schedule-loop1 mm (rng 2 2) rr)))
           :in-theory (e/d (isr-step)
                           (aes-fixslice-encrypt-inv-shift-rows-1-at
                            aes-fixslice-encrypt-inv-shift-rows-2-at
                            aes-fixslice-encrypt-inv-shift-rows-3-at
                            aes-fixslice-encrypt-inv-shift-rows-1
                            aes-fixslice-encrypt-inv-shift-rows-2
                            aes-fixslice-encrypt-inv-shift-rows-3
                            w8-spec rd8 nth
                            (:executable-counterpart core-ops-range-range-usize-))))))

;; result-p facts (the fty equality (equal x (ok v)) decomposes into
;; result-p x + kind + val; the loop needs its own return-type fact).
(defthm result-p-of-write8-loop0
  (result-p (aes-fixslice-encrypt-write8-loop0 n iter rkeys off s))
  :hints (("Goal" :induct (aes-fixslice-encrypt-write8-loop0 n iter rkeys off s))))
(defthm result-p-of-sbn-at
  (result-p (aes-fixslice-encrypt-sub-bytes-nots-at n rk off)))
(defthm result-p-of-ks-loop2
  (result-p (aes-fixslice-encrypt-aes128-key-schedule-loop2 n iter rk off))
  :hints (("Goal" :induct (aes-fixslice-encrypt-aes128-key-schedule-loop2 n iter rk off)
           :in-theory (disable aes-fixslice-encrypt-sub-bytes-nots-at))))

;; ---------------------------------------------------------------------------
;; loop2 (the NOTs) IS sbn-chain, by induction (off in lockstep with i).
(defun sbn-li (m i rk off)
  (declare (xargs :measure (nfix (- 11 (nfix i)))))
  (if (or (not (natp i)) (>= i 11)) (list m i rk off)
    (sbn-li (1- m) (1+ i)
            (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots-at 100 rk off))
            (+ off 8))))

(defthm ks-loop2-is-sbn-chain
  (implies (and (natp i) (<= 1 i) (<= i 11) (equal off (* 8 i)) (equal (len rk) 88)
                (natp m) (< (+ 12 (- 11 i)) m))
           (equal (aes-fixslice-encrypt-aes128-key-schedule-loop2 m (rng i 11) rk off)
                  (ok (sbn-chain rk off i))))
  :hints (("Goal" :induct (sbn-li m i rk off)
           :in-theory (e/d (sbn-chain)
                           (aes-fixslice-encrypt-sub-bytes-nots-at
                            aes-fixslice-encrypt-sub-bytes-nots
                            sub-bytes-nots-at-form-n
                            w8-spec rd8 nth wstatep
                            (:executable-counterpart core-ops-range-range-usize-))))
          ("Subgoal *1/2"
           :expand ((:free (xoff) (aes-fixslice-encrypt-aes128-key-schedule-loop2 m (rng i 11) rk xoff))
                    (:free (xoff) (sbn-chain rk xoff i))))
          ("Subgoal *1/1"
           :expand ((:free (xoff) (aes-fixslice-encrypt-aes128-key-schedule-loop2 m (rng i 11) rk xoff))
                    (:free (xoff) (sbn-chain rk xoff i))))))

;; ---------------------------------------------------------------------------
;; (4) THE DECOMPOSITION.  With all three loops collapsed, the schedule body
;; is 8 binds and the last expression is loop2 itself, so the collapse ends in
;; (ok (sbn-chain ...)) with no constructor residue.
(defund ks-fold2 (w)
  (sbn-chain
    (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1-at 100
      (isr-step (isr-step w 8) 40) 72))
    8 1))

(defthm rk-of-ok2 (equal (result-kind (result-ok x)) :ok))

(defthm ks-decomp
  (implies (aes::inp key)
           (equal (aes-fixslice-encrypt-aes128-key-schedule 100 key)
                  (ok (ks-fold2 (kr-chain (result-ok->val
                                 (aes-fixslice-encrypt-bitslice-into 100 (array-repeat 88 0) 0 key key))
                               0 0)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'ground-zero)
                        '((:definition aes-fixslice-encrypt-aes128-key-schedule)
                          (:definition ks-fold2)
                          (:definition core-iter-traits-collect-impl-core-iter-traits-collect-intoiterator-for-core-ops-range-range-usize-into-iter-core-ops-range-range-usize-)
                          (:definition not)
                          (:rewrite len-of-array-repeat)
                          (:rewrite result-kind-of-seed) (:rewrite len-of-seed) (:rewrite len-of-core)
                          (:rewrite true-listp-of-seed)
                          (:rewrite ks-loop0-is-kr-chain)
                          (:rewrite ks-loop1-collapse)
                          (:rewrite ks-loop2-is-sbn-chain)
                          (:rewrite len-of-isr-step)
                          (:rewrite result-kind-of-isr1-at-len) (:rewrite len-of-isr1-at-len)
                          (:rewrite result-ok->val-of-result-ok)
                          (:rewrite rk-of-ok2)
                          (:executable-counterpart nfix) (:executable-counterpart zp)
                          (:executable-counterpart binary-+) (:executable-counterpart binary-*)
                          (:executable-counterpart <) (:executable-counterpart unary--)
                          (:executable-counterpart natp) (:executable-counterpart integerp)
                          (:executable-counterpart equal) (:executable-counterpart eq))))))
