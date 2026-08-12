; Phase 4 -- key-schedule: ONE key_round == the off-independent window transform
; krw8, verified for ALL inputs.  Composes the op layer (aes_fixslice_keyops)
; into a single characterisation of key_round(rkeys,off,c):
;   * key-round-unfold : the whole round is xor_columns over the arcon of the
;     sub_bytes_nots of the sub_bytes of the previous window (memshift copies it)
;   * key-round-car     : returns offset off+8
;   * key-round-window  : rkeys[off+8..off+16) := krw8(rkeys[off..off+8), c)
;   * key-round-frame-below / key-round-len : everything below off+8 (all earlier
;     round keys) is preserved; length unchanged
;   * wstatep-of-krw8   : the new window is again a wstate (8 u32) -- the loop
;     invariant the 10-round chain threads (bitslice of the key seeds it)
; krw8 is off-INDEPENDENT: exactly the transform the keycore step cruxes prove
; equals the AES key-expansion recurrence at off=0, so the chain lifts each of
; the 10 concrete offsets to Kestrel's keyexpansion.  All structured rewriting;
; GL only for the irreducible per-op bit facts (S-box, xc-word, bitslice range).
(in-package "ACL2")
(include-book "aes_fixslice_keyops")
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/update-nth" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))
(local (in-theory (disable nth-when-zp)))

;; Connector rules so key_round's hyp relief is one-step at each op: the window
;; read after each op is a wstate, expressed against the previous window.
(defthm wstatep-rd8-after-memshift
  (implies (and (natp src) (wstatep (rd8 buffer src)))
           (wstatep (rd8 (ms-spec 0 8 buffer src (+ src 8)) (+ src 8)))))
(defthm wstatep-rd8-after-w8spec-sub
  (implies (and (natp off) (wstatep s))
           (wstatep (rd8 (w8-spec 0 8 rkeys off s) off)))
  :hints (("Goal" :in-theory (disable w8-spec))))

(defthm true-listp-of-ms-spec
  (implies (true-listp buffer) (true-listp (ms-spec i e buffer src dst))))

;; every schedule call site is 8-aligned; discharge memshift's debug_assert
;; hypothesis automatically at (* 8 i) offsets (and by evaluation at literals).
(defthm rem-8i (implies (natp i) (equal (rem (* 8 i) 8) 0)))

;; key_round writes only rkeys[off+8..off+16); that window is the xor_columns
;; recurrence over the arcon(subnots(subbytes(prev-window))) value.
(defthm key-round-unfold
  (implies (and (natp off) (equal (rem off 8) 0)
                (<= (+ off 16) (len rkeys)) (< (len rkeys) 4294967296)
                (true-listp rkeys) (wstatep (rd8 rkeys off)) (natp c) (< c 12))
           (equal (aes-fixslice-encrypt-key-round 100 rkeys off c)
                  (ok (cons (+ off 8)
                            (xc-spec 0 8
                              (w8-spec 0 8 (ms-spec 0 8 rkeys off (+ off 8)) (+ off 8)
                                (arc-list (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots
                                            (result-ok->val (aes-fixslice-encrypt-sub-bytes (rd8 rkeys off))))) c))
                              (+ off 8) 8 (result-ok->val (aes-fixslice-encrypt-ror-distance 1 3)))))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (aes-fixslice-encrypt-key-round)
                                  (w8-spec ms-spec xc-spec nth
                                   aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-sub-bytes-nots
                                   aes-fixslice-encrypt-add-round-constant-bit
                                   aes-fixslice-encrypt-xor-columns aes-fixslice-encrypt-memshift32
                                   aes-fixslice-encrypt-sub-bytes-at aes-fixslice-encrypt-sub-bytes-nots-at
                                   aes-fixslice-encrypt-add-rcon)))))

;; The off-independent window transform one key_round applies.
(defund krw8 (s8 c)
  (b* ((sb  (result-ok->val (aes-fixslice-encrypt-sub-bytes s8)))
       (sbn (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots sb)))
       (d   (arc-list sbn c))
       ((ok dror) (aes-fixslice-encrypt-ror-distance 1 3)))
    (list (xc-word (nth 0 s8) (nth 0 d) dror) (xc-word (nth 1 s8) (nth 1 d) dror)
          (xc-word (nth 2 s8) (nth 2 d) dror) (xc-word (nth 3 s8) (nth 3 d) dror)
          (xc-word (nth 4 s8) (nth 4 d) dror) (xc-word (nth 5 s8) (nth 5 d) dror)
          (xc-word (nth 6 s8) (nth 6 d) dror) (xc-word (nth 7 s8) (nth 7 d) dror))))

(defthm key-round-car
  (implies (and (natp off) (equal (rem off 8) 0)
                (<= (+ off 16) (len rkeys)) (< (len rkeys) 4294967296)
                (true-listp rkeys) (wstatep (rd8 rkeys off)) (natp c) (< c 12))
           (equal (car (result-ok->val (aes-fixslice-encrypt-key-round 100 rkeys off c)))
                  (+ off 8)))
  :hints (("Goal" :do-not-induct t
                  :use ((:instance key-round-unfold))
                  :in-theory (disable key-round-unfold aes-fixslice-encrypt-key-round
                                      w8-spec ms-spec xc-spec nth arc-list rd8
                                      aes-fixslice-encrypt-sub-bytes
                                      aes-fixslice-encrypt-sub-bytes-nots
                                      aes-fixslice-encrypt-ror-distance))))

;; The new window rkeys[off+8..off+16) after one key_round == krw8(prev window).
(defthm key-round-window
  (implies (and (natp off) (equal (rem off 8) 0)
                (<= (+ off 16) (len rkeys)) (< (len rkeys) 4294967296)
                (true-listp rkeys) (wstatep (rd8 rkeys off)) (natp c) (< c 12))
           (equal (rd8 (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100 rkeys off c))) (+ off 8))
                  (krw8 (rd8 rkeys off) c)))
  :hints (("Goal" :do-not-induct t
                  :use ((:instance key-round-unfold))
                  :in-theory (e/d (rd8 krw8)
                                  (key-round-unfold aes-fixslice-encrypt-key-round
                                   w8-spec ms-spec xc-spec nth arc-list
                                   aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-sub-bytes-nots
                                   aes-fixslice-encrypt-ror-distance)))))

(defthm key-round-len
  (implies (and (natp off) (equal (rem off 8) 0)
                (<= (+ off 16) (len rkeys)) (< (len rkeys) 4294967296)
                (true-listp rkeys) (wstatep (rd8 rkeys off)) (natp c) (< c 12))
           (equal (len (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100 rkeys off c))))
                  (len rkeys)))
  :hints (("Goal" :do-not-induct t
                  :use ((:instance key-round-unfold))
                  :in-theory (disable key-round-unfold aes-fixslice-encrypt-key-round
                                      w8-spec ms-spec xc-spec nth arc-list rd8
                                      aes-fixslice-encrypt-sub-bytes
                                      aes-fixslice-encrypt-sub-bytes-nots
                                      aes-fixslice-encrypt-ror-distance))))

;; FRAME: positions strictly below the written window are unchanged, so earlier
;; round keys survive each subsequent key_round.
(defthm key-round-frame-below
  (implies (and (natp off) (equal (rem off 8) 0)
                (<= (+ off 16) (len rkeys)) (< (len rkeys) 4294967296)
                (true-listp rkeys) (wstatep (rd8 rkeys off)) (natp c) (< c 12)
                (natp k) (< k (+ off 8)))
           (equal (nth k (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100 rkeys off c))))
                  (nth k rkeys)))
  :hints (("Goal" :do-not-induct t
                  :use ((:instance key-round-unfold))
                  :in-theory (disable key-round-unfold aes-fixslice-encrypt-key-round
                                      w8-spec ms-spec xc-spec nth arc-list rd8
                                      aes-fixslice-encrypt-sub-bytes
                                      aes-fixslice-encrypt-sub-bytes-nots
                                      aes-fixslice-encrypt-ror-distance))))

;; xc-word maps u32s to a u32 (all ops mod-2^32); GL at the concrete rotation
;; ror_distance(1,3)=14 that krw8 uses (a symbolic amount blows up the BDDs).
(gl::def-gl-thm u32p-of-xc-word-gl
  :hyp (and (unsigned-byte-p 32 left) (unsigned-byte-p 32 cur))
  :concl (unsigned-byte-p 32 (xc-word left cur 14))
  :g-bindings (gl::auto-bindings (:nat left 32) (:nat cur 32)))
(defthm u32p-of-xc-word
  (implies (and (unsigned-byte-p 32 left) (unsigned-byte-p 32 cur))
           (unsigned-byte-p 32 (xc-word left cur 14)))
  :hints (("Goal" :use u32p-of-xc-word-gl :in-theory (disable u32p-of-xc-word-gl xc-word))))

(defthm ror-distance-1-3 (equal (aes-fixslice-encrypt-ror-distance 1 3) (ok 14)))

;; extract a u32 element from a wstate at a literal index (syntaxp: no looping)
(defthm u32-nth-of-wstatep
  (implies (and (syntaxp (quotep k)) (wstatep x) (natp k) (< k 8))
           (unsigned-byte-p 32 (nth k x)))
  :hints (("Goal" :in-theory (enable wstatep)
           :cases ((equal k 0) (equal k 1) (equal k 2) (equal k 3)
                   (equal k 4) (equal k 5) (equal k 6) (equal k 7)))))
;; build a wstate from 8 u32s
(defthm wstatep-of-list8
  (implies (and (unsigned-byte-p 32 e0) (unsigned-byte-p 32 e1) (unsigned-byte-p 32 e2) (unsigned-byte-p 32 e3)
                (unsigned-byte-p 32 e4) (unsigned-byte-p 32 e5) (unsigned-byte-p 32 e6) (unsigned-byte-p 32 e7))
           (wstatep (list e0 e1 e2 e3 e4 e5 e6 e7)))
  :hints (("Goal" :in-theory (enable wstatep))))

;; krw8 maps a wstate to a wstate (ror_distance(1,3) computes to 14).
(defthm wstatep-of-krw8
  (implies (and (wstatep s8) (natp c) (< c 12)) (wstatep (krw8 s8 c)))
  :hints (("Goal" :in-theory (e/d (krw8) (wstatep xc-word arc-list nth
                                   aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-sub-bytes-nots))
                  :use ((:instance wstatep-of-arc-list
                          (s8 (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots
                                (result-ok->val (aes-fixslice-encrypt-sub-bytes s8)))))))
                  :do-not-induct t)))

;; bitslice of two 16-byte blocks is a wstate (8 u32) -- GL + expand-len-16 lift.
(gl::def-gl-thm wstatep-of-bitslice-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15)
            (unsigned-byte-p 8 b0) (unsigned-byte-p 8 b1) (unsigned-byte-p 8 b2) (unsigned-byte-p 8 b3) (unsigned-byte-p 8 b4) (unsigned-byte-p 8 b5) (unsigned-byte-p 8 b6) (unsigned-byte-p 8 b7) (unsigned-byte-p 8 b8) (unsigned-byte-p 8 b9) (unsigned-byte-p 8 b10) (unsigned-byte-p 8 b11) (unsigned-byte-p 8 b12) (unsigned-byte-p 8 b13) (unsigned-byte-p 8 b14) (unsigned-byte-p 8 b15))
  :concl (and (equal (result-kind (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0)
                       (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)
                       (list b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15))) :ok)
              (wstatep (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0)
                       (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)
                       (list b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8) (:nat b0 8) (:nat b1 8) (:nat b2 8) (:nat b3 8) (:nat b4 8) (:nat b5 8) (:nat b6 8) (:nat b7 8) (:nat b8 8) (:nat b9 8) (:nat b10 8) (:nat b11 8) (:nat b12 8) (:nat b13 8) (:nat b14 8) (:nat b15 8)))

;; ---------------------------------------------------------------------------
;; ROADMAP -- remaining for  key_schedule core == bitslice(keyexpansion):
;; 1. krw8-crux-c (c=0..9): car(inv_bitslice(krw8(bitslice(b,b), c))) =
;;    kr-spec-bytes(b, xpow c), for any 16-byte b.  Derived from the keycore
;;    step crux (off=0, rk0 = append(bitslice(b,b), 80 zeros)) by rewriting the
;;    crux's key_round with key-round-window (rd8(rk1,8) = krw8(bitslice(b,b),c))
;;    and take-8-nthcdr = rd8; then expand-len-16 to generalise from the 16
;;    symbolic bytes to any (inp b).  kr-spec-bytes iterated = Kestrel
;;    keyexpansion is already validated in keycore.
;; 2. The 10-round chain: bitslice-into seeds window 0 = bitslice(key,key)
;;    (wstatep-of-bitslice); each key_round writes the next window = krw8(prev)
;;    (key-round-window) while preserving all earlier windows (key-round-frame-
;;    below) and keeping the new window a wstate (wstatep-of-krw8).  So
;;    inv_bitslice(window r) = kk(r) for r=0..10 by unfolding the 10 concrete
;;    offsets (read-over-write on rd8 at 0,8,...,80).
;; 3. Combine with aes_fixslice_keyschedule's fold layer (sub_bytes_nots = xor63,
;;    inv_shift_rows_i = invshiftrows^i) to replace that book's concrete
;;    assert-event with the all-inputs aes128_key_schedule correspondence.
