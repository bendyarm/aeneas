; Phase 4 -- key schedule CORE chain: the extracted 10 key_rounds compute
; Kestrel's key expansion, bitsliced, for ALL inputs.
;
; MAIN THEOREM (core-windows-are-bitslice-of-keyexpansion):
;   (aes::inp key) =>
;     (wok (kr-chain (bitslice-into 88-zeros 0 key key) 0 0) key 80 10)
; i.e. running the extracted seed (bitslice(key,key) into window 0) and the ten
; key_rounds fills EVERY window r (r = 0..10) with bitslice(kk_r,kk_r), where
; kk_r = kk-iter(key,r) is the iterated AES key-expansion recurrence.  So the
; fixslice key-schedule core is exactly Kestrel's key expansion, bitsliced.
;
; STRUCTURE:
;   (1) step-star   : one key_round advances a symmetric window (c-uniform).
;   (2) inp-of-kk-iter / kx-byte : the recurrence stays inp; rcons are bytes.
;   (4) kr-chain / wok : the recursive core model + window-invariant predicate.
;   (5) wok-of-key-round-below : a round preserves windows at/below its offset,
;       via the congruence wok-cong (wok reads only rd8) + the frame reads
;       rd8-agree-of-key-round-below (keyframe's rd8-of-key-round-below erases the
;       key_round term per level, so the wok induction never sees the huge body).
;   (6) wok-of-key-round : a round EXTENDS the invariant by one window
;       (key-round-window + step-star + kk-iter-step; wok-construct assembles it).
;   (7) kr-chain-wok : threads (5)+(6) through the 10 rounds (off = 8i via
;       key-round-car), and the seed seeds window 0 = bitslice(kk_0,kk_0).
; The frame primitives that want arithmetic-5 live in aes_fixslice_keyframe;
; this book runs on ground-zero linear arithmetic (arithmetic-5 explodes the
; 8-strided offset inductions), with an offset/index (off,i) wok formulation.
(in-package "ACL2")
(include-book "aes_fixslice_keyframe")
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/append" :dir :system))
;; NB: no arithmetic-5 here -- its aggressive subtraction/nonlinear case splits
;; explode the wok inductions over the 8-strided window offsets.  ground-zero
;; linear arithmetic suffices for the (linear) offset reasoning; the rd8/
;; true-listp frame lemmas that DO want arithmetic-5 live in aes_fixslice_keyframe.
(local (in-theory (disable len-when-wstatep true-listp-when-wstatep nth-when-zp)))

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
  ;; measure hint pinned: the governing bitslice-window hypothesis otherwise
  ;; drags the whole gate network into the (trivial) measure conjecture.
  (declare (xargs :measure (nfix i)
                  :hints (("Goal" :in-theory (theory 'ground-zero)))))
  (if (zp i)
      (equal (rd8 rk off)
             (result-ok->val (aes-fixslice-encrypt-bitslice (kk-iter key 0) (kk-iter key 0))))
    (and (equal (rd8 rk off)
                (result-ok->val (aes-fixslice-encrypt-bitslice (kk-iter key i) (kk-iter key i))))
         (wok rk key (nfix (- off 8)) (1- i)))))

;; the stepped-down offset stays a nat bounded by the original.
(defthm nfix-off-8-lte
  (implies (natp off) (<= (nfix (- off 8)) off))
  :rule-classes :linear)

;; explicit induction scheme mirroring wok's recursion (so wok/rd8-agree stay
;; DISABLED in the inductions, keeping tails folded to match the IH).
(defun wok-induct (off i)
  (declare (xargs :measure (nfix i)))
  (if (zp i) (list off i) (wok-induct (nfix (- off 8)) (1- i))))

;; rd8-agree rk2 rk off i  <=>  rk2 and rk read the same 8-word window at off,
;; off-8, ..., down i+1 levels.  wok depends on rk ONLY through these reads, so a
;; congruence lets us prove the key_round frame WITHOUT the big key_round term
;; ever entering the wok induction (which otherwise clausifies enormously).
(defun rd8-agree (rk2 rk off i)
  (declare (xargs :measure (nfix i)))
  (if (zp i) (equal (rd8 rk2 off) (rd8 rk off))
    (and (equal (rd8 rk2 off) (rd8 rk off))
         (rd8-agree rk2 rk (nfix (- off 8)) (1- i)))))

;; (5a) congruence: wok sees only the rd8 reads, so agreeing arrays agree on wok.
;;      Generic rk/rk2 -- no big term, cheap clausification.
(defthm wok-cong
  (implies (and (wok rk key off i) (rd8-agree rk2 rk off i))
           (wok rk2 key off i))
  :hints (("Goal" :induct (wok-induct off i)
           :in-theory (disable wok rd8-agree rd8 aes-fixslice-encrypt-bitslice kk-iter nth))
          ("Subgoal *1/2" :expand ((wok rk key off i) (wok rk2 key off i)
                                    (rd8-agree rk2 rk off i)))
          ("Subgoal *1/1" :expand ((wok rk key off i) (wok rk2 key off i)
                                    (rd8-agree rk2 rk off i)))))

;; (5b) the frame reads: a key_round at off0 leaves every read at or below off0
;;      unchanged.  rd8-of-key-round-below rewrites the big term away per level,
;;      so the induction clause stays small.
(defthm rd8-agree-of-key-round-below
  (implies (and (natp off0) (equal (rem off0 8) 0)
                (<= (+ off0 16) (len rkeys)) (< (len rkeys) 4294967296)
                (true-listp rkeys) (wstatep (rd8 rkeys off0)) (natp c) (< c 12)
                (natp off) (<= off off0))
           (rd8-agree (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100 rkeys off0 c)))
                      rkeys off i))
  ;; key-round-unfold MUST stay disabled: it would rewrite (key_round ...) into
  ;; its giant xc/w8/ms-spec form, after which rd8-of-key-round-below no longer
  ;; matches and the huge term clausifies.  Keep key_round opaque so the frame
  ;; rewrite fires and the term is erased per level.
  :hints (("Goal" :induct (wok-induct off i)
           :in-theory (disable rd8-agree aes-fixslice-encrypt-key-round key-round-unfold
                               rd8 wstatep nth))
          ("Subgoal *1/2"
           :expand ((rd8-agree (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100 rkeys off0 c)))
                               rkeys off i)))
          ("Subgoal *1/1"
           :expand ((rd8-agree (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100 rkeys off0 c)))
                               rkeys off i)))))

;; (5) a key_round at offset off0 preserves every window at or below off0.
(defthm wok-of-key-round-below
  (implies (and (natp off0) (equal (rem off0 8) 0)
                (<= (+ off0 16) (len rkeys)) (< (len rkeys) 4294967296)
                (true-listp rkeys) (wstatep (rd8 rkeys off0)) (natp c) (< c 12)
                (natp off) (<= off off0) (wok rkeys key off i))
           (wok (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100 rkeys off0 c)))
                key off i))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable wok rd8-agree aes-fixslice-encrypt-key-round rd8)
           :use ((:instance wok-cong
                   (rk rkeys)
                   (rk2 (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100 rkeys off0 c)))))
                 rd8-agree-of-key-round-below))))

;; the top window recorded by wok (both the zp and non-zp branches store
;; rd8 rk off = bitslice(kk_i,kk_i) for natp i, since kk-iter key 0 = key).
(defthm wok-top
  (implies (and (wok rk key off i) (natp i))
           (equal (rd8 rk off)
                  (result-ok->val (aes-fixslice-encrypt-bitslice (kk-iter key i) (kk-iter key i)))))
  :hints (("Goal" :expand ((wok rk key off i))
           :in-theory (disable rd8 aes-fixslice-encrypt-bitslice kk-iter nth))))

(defthm natp-nfix-id (implies (natp x) (equal (nfix x) x)))

;; the kk-iter step as a rewrite (fires wherever kk-iter key (1+i) appears, e.g.
;; in the reconstructed goal, so it lines up with step-star's kr-spec output).
(defthm kk-iter-step
  (implies (natp i)
           (equal (kk-iter key (+ 1 i)) (kr-spec-bytes (kk-iter key i) (kx i))))
  :hints (("Goal" :expand ((kk-iter key (+ 1 i)))
           :in-theory (disable kr-spec-bytes kx))))

;; build a wok from its top window (rd8 rk off = bitslice(kk_i)) and its tail.
(defthm wok-construct
  (implies (and (not (zp i))
                (equal (rd8 rk off)
                       (result-ok->val (aes-fixslice-encrypt-bitslice (kk-iter key i) (kk-iter key i))))
                (wok rk key (nfix (- off 8)) (1- i)))
           (wok rk key off i))
  :hints (("Goal" :expand ((wok rk key off i))
           :in-theory (disable rd8 aes-fixslice-encrypt-bitslice kk-iter nth))))

;; ---------------------------------------------------------------------------
;; (6) a key_round at off0 (rcon i) EXTENDS the invariant by one window:
;;     the new window at off0+8 is bitslice(kk_{i+1},kk_{i+1}), and windows 0..i
;;     survive (5).  Uses key-round-window (new window = krw8(prev)), step-star
;;     (krw8(bitslice(b,b),i) = bitslice(kr(b),kr(b))) and the kk-iter step.
(defthm wok-of-key-round
  (implies (and (aes::inp key) (natp i) (< i 10) (natp off0) (<= off0 72)
                (equal (rem off0 8) 0)
                (equal (len rkeys) 88) (true-listp rkeys)
                (wok rkeys key off0 i))
           (wok (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100 rkeys off0 i)))
                key (+ off0 8) (+ i 1)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable wok wok-cong rd8-agree aes-fixslice-encrypt-key-round
                               key-round-unfold krw8 aes-fixslice-encrypt-bitslice
                               rd8 kk-iter wstatep nth kr-spec-bytes)
           ;; new window from key-round-window + step-star + wok-top + kk-iter-step
           ;; (rewrite); windows 0..i survive by (5); wok-construct assembles it.
           :use ((:instance wok-top (rk rkeys) (off off0) (i i))
                 (:instance key-round-window (rkeys rkeys) (off off0) (c i))
                 (:instance step-star (b (kk-iter key i)) (c i))
                 (:instance inp-of-kk-iter (key key) (r i))
                 (:instance wstatep-of-bitslice (b0 (kk-iter key i)) (b1 (kk-iter key i)))
                 (:instance wok-of-key-round-below (rkeys rkeys) (off0 off0) (c i)
                            (off off0) (i i))
                 (:instance wok-construct
                            (rk (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100 rkeys off0 i))))
                            (off (+ off0 8)) (i (+ i 1)))))))

;; ---------------------------------------------------------------------------
;; (7) thread (5)+(6) through kr-chain: off = 8i is maintained by key-round-car,
;; and every round extends the invariant, so kr-chain(rk,0,0) fills all 11
;; windows.  A few 8*i facts (kept off arithmetic-5) and a wstatep-from-wok rule.
(defthm mul-8-natp (implies (natp i) (natp (* 8 i))) :rule-classes :type-prescription)
(defthm mul-8-distrib (equal (* 8 (+ 1 i)) (+ 8 (* 8 i))))
(defthm mul-8-le-72 (implies (and (natp i) (< i 10)) (<= (* 8 i) 72)))

(defthm wstatep-rd8-of-wok
  (implies (and (aes::inp key) (wok rk key off i) (natp i) (<= i 10))
           (wstatep (rd8 rk off)))
  :hints (("Goal" :in-theory (disable rd8 aes-fixslice-encrypt-bitslice kk-iter wok wstatep nth)
           :use ((:instance wok-top (rk rk) (off off) (i i))
                 (:instance inp-of-kk-iter (key key) (r i))
                 (:instance wstatep-of-bitslice (b0 (kk-iter key i)) (b1 (kk-iter key i)))))))

(defthm kr-chain-wok
  (implies (and (aes::inp key) (natp i) (<= i 10) (equal off (* 8 i))
                (equal (len rk) 88) (true-listp rk) (wok rk key off i))
           (wok (kr-chain rk off i) key 80 10))
  :hints (("Goal" :induct (kr-chain rk off i)
           :in-theory (e/d (kr-chain)
                           (aes-fixslice-encrypt-key-round key-round-unfold rd8
                            aes-fixslice-encrypt-bitslice kk-iter krw8 wstatep nth
                            kr-spec-bytes wok wok-cong rd8-agree)))
          ;; the step: this round extends the invariant (wok-of-key-round) and
          ;; car/len/true-listp keep the offset = 8*(i+1) and the array well-formed
          ;; so the IH applies at the next window.
          ("Subgoal *1/2"
           :use ((:instance wok-of-key-round (rkeys rk) (off0 (* 8 i)) (i i))
                 (:instance key-round-car (rkeys rk) (off (* 8 i)) (c i))
                 (:instance key-round-len (rkeys rk) (off (* 8 i)) (c i))
                 (:instance true-listp-of-cdr-key-round (rkeys rk) (off (* 8 i)) (c i))
                 (:instance wstatep-rd8-of-wok (rk rk) (key key) (off (* 8 i)) (i i))))))

;; ---------------------------------------------------------------------------
;; The seed: bitslice(key,key) written into an 88-word zero array (window 0).
(defthm true-listp-of-array-repeat (true-listp (array-repeat n x)))

;; bitslice of two inp blocks never fails (GL fact lifted, as wstatep-of-bitslice).
(defthm bitslice-ok
  (implies (and (aes::inp b0) (aes::inp b1))
           (equal (result-kind (aes-fixslice-encrypt-bitslice b0 b1)) :ok))
  :hints (("Goal"
           :in-theory (e/d (expand-len-16)
                           (wstatep-of-bitslice-gl aes-fixslice-encrypt-bitslice wstatep nth aes::inp))
           :use ((:instance wstatep-of-bitslice-gl
                  (a0 (nth 0 b0)) (a1 (nth 1 b0)) (a2 (nth 2 b0)) (a3 (nth 3 b0)) (a4 (nth 4 b0)) (a5 (nth 5 b0)) (a6 (nth 6 b0)) (a7 (nth 7 b0)) (a8 (nth 8 b0)) (a9 (nth 9 b0)) (a10 (nth 10 b0)) (a11 (nth 11 b0)) (a12 (nth 12 b0)) (a13 (nth 13 b0)) (a14 (nth 14 b0)) (a15 (nth 15 b0))
                  (b0 (nth 0 b1)) (b1 (nth 1 b1)) (b2 (nth 2 b1)) (b3 (nth 3 b1)) (b4 (nth 4 b1)) (b5 (nth 5 b1)) (b6 (nth 6 b1)) (b7 (nth 7 b1)) (b8 (nth 8 b1)) (b9 (nth 9 b1)) (b10 (nth 10 b1)) (b11 (nth 11 b1)) (b12 (nth 12 b1)) (b13 (nth 13 b1)) (b14 (nth 14 b1)) (b15 (nth 15 b1)))
                 (:instance unsigned-byte-p-8-of-nth-when-inp (x b0) (i 0)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b0) (i 1)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b0) (i 2)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b0) (i 3)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b0) (i 4)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b0) (i 5)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b0) (i 6)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b0) (i 7)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b0) (i 8)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b0) (i 9)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b0) (i 10)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b0) (i 11)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b0) (i 12)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b0) (i 13)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b0) (i 14)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b0) (i 15)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b1) (i 0)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b1) (i 1)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b1) (i 2)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b1) (i 3)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b1) (i 4)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b1) (i 5)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b1) (i 6)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b1) (i 7)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b1) (i 8)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b1) (i 9)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b1) (i 10)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b1) (i 11)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b1) (i 12)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b1) (i 13)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b1) (i 14)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b1) (i 15))))))

(defthm len-of-seed
  (implies (aes::inp key)
           (equal (len (result-ok->val
                    (aes-fixslice-encrypt-bitslice-into 100 (array-repeat 88 0) 0 key key)))
                  88))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-bitslice-into)
                                  (aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-write8 aes-fixslice-encrypt-write8-loop0 w8-spec rd8 wstatep nth))
           :use ((:instance wstatep-of-bitslice (b0 key) (b1 key))
                 (:instance write8-is-w8spec (rkeys (array-repeat 88 0)) (off 0)
                            (s (result-ok->val (aes-fixslice-encrypt-bitslice key key))))
                 (:instance len-of-w8-spec (i 0) (e 8) (rkeys (array-repeat 88 0)) (off 0)
                            (s (result-ok->val (aes-fixslice-encrypt-bitslice key key))))))))

(defthm true-listp-of-seed
  (implies (aes::inp key)
           (true-listp (result-ok->val
                    (aes-fixslice-encrypt-bitslice-into 100 (array-repeat 88 0) 0 key key))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-bitslice-into)
                                  (aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-write8 aes-fixslice-encrypt-write8-loop0 w8-spec rd8 wstatep nth))
           :use ((:instance wstatep-of-bitslice (b0 key) (b1 key))
                 (:instance write8-is-w8spec (rkeys (array-repeat 88 0)) (off 0)
                            (s (result-ok->val (aes-fixslice-encrypt-bitslice key key))))))))

(defthm rd8-of-seed
  (implies (aes::inp key)
           (equal (rd8 (result-ok->val
                    (aes-fixslice-encrypt-bitslice-into 100 (array-repeat 88 0) 0 key key)) 0)
                  (result-ok->val (aes-fixslice-encrypt-bitslice key key))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-bitslice-into)
                                  (aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-write8 aes-fixslice-encrypt-write8-loop0 w8-spec wstatep nth))
           :use ((:instance wstatep-of-bitslice (b0 key) (b1 key))
                 (:instance write8-is-w8spec (rkeys (array-repeat 88 0)) (off 0)
                            (s (result-ok->val (aes-fixslice-encrypt-bitslice key key))))
                 (:instance rd8-of-w8spec-same (off 0) (rkeys (array-repeat 88 0))
                            (s (result-ok->val (aes-fixslice-encrypt-bitslice key key))))))))

;; window 0 = bitslice(kk_0,kk_0) since kk_0 = key.
(defthm wok-of-seed
  (implies (aes::inp key)
           (wok (result-ok->val
                  (aes-fixslice-encrypt-bitslice-into 100 (array-repeat 88 0) 0 key key))
                key 0 0))
  ;; base case (index 0): enable wok/kk-iter to unfold at 0 (kk_0 = key); the
  ;; single read is supplied by rd8-of-seed.  Big functions stay closed.
  :hints (("Goal" :in-theory (e/d (wok kk-iter)
                                  (aes-fixslice-encrypt-bitslice-into rd8
                                   aes-fixslice-encrypt-bitslice nth))
           :use rd8-of-seed)))

;; ===========================================================================
;; MILESTONE A: the extracted key-schedule core -- seed then 10 key_rounds --
;; fills EVERY window r (r = 0..10) with bitslice(kk_r, kk_r), for ALL inputs.
;; I.e. the fixslice key expansion computes Kestrel's key expansion, bitsliced.
;; ===========================================================================
(defthm core-windows-are-bitslice-of-keyexpansion
  (implies (aes::inp key)
           (wok (kr-chain (result-ok->val
                            (aes-fixslice-encrypt-bitslice-into 100 (array-repeat 88 0) 0 key key))
                          0 0)
                key 80 10))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable kr-chain wok aes-fixslice-encrypt-bitslice-into)
           :use (wok-of-seed len-of-seed true-listp-of-seed
                 (:instance kr-chain-wok
                            (rk (result-ok->val
                                  (aes-fixslice-encrypt-bitslice-into 100 (array-repeat 88 0) 0 key key)))
                            (off 0) (i 0))))))
