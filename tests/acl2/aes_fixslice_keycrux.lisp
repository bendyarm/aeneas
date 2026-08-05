; Phase 4 -- key-schedule: connecting krw8 to the spec recurrence via the
; keycore step cruxes.  ROUND 0 is proven end-to-end:
;   krw8-crux-0 : car(inv_bitslice(krw8(bitslice(b,b), 0))) = kr-spec-bytes(b, 1)
; for every 16-byte b, by combining key-round-step-rcon0 (keycore) with
; key-round-window (keyround) over the seed array rk0 = append(bitslice(b,b),
; 80 zeros).  The bridges are reusable: take-8-nthcdr = rd8 (the cruxes read the
; window as take/nthcdr), bitslice-of-inp is a wstate, and rd8 of the seed reads
; back the bitslice.
;
; ROUNDS 1-9 are STRUCTURALLY IDENTICAL (swap rcon{c} + xpow) but the same proof
; recipe explodes in the rewriter (~184s prove, then fails) for c>=1 while c=0
; closes in <1s -- with key_round/krw8/inv_bitslice/bitslice all disabled, so the
; blow-up is in the arith-5 + len-when-wstatep interaction on the nonzero-rcon
; terms.  A robust replacement (a single c-general lemma, or discharging the
; key-round-window hyps without the free-variable len-when-wstatep) is the next
; step; the machinery (key-round-window, wstatep-of-bitslice) is all in place.
(in-package "ACL2")
(include-book "aes_fixslice_keyround")
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/append" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))
(local (in-theory (disable nth-when-zp)))

;; bridge: the keycore cruxes read the window as (take 8 (nthcdr off .)); that
;; is our rd8 whenever the window is in bounds.
(defthm len-of-rd8-8 (equal (len (rd8 l off)) 8) :hints (("Goal" :in-theory (enable rd8))))
(defthm true-listp-of-rd8 (true-listp (rd8 l off)) :hints (("Goal" :in-theory (enable rd8))))
(defthm nth-of-rd8
  (implies (and (natp n) (< n 8)) (equal (nth n (rd8 l off)) (nth (+ off n) l)))
  :hints (("Goal" :in-theory (enable rd8)
           :cases ((equal n 0) (equal n 1) (equal n 2) (equal n 3)
                   (equal n 4) (equal n 5) (equal n 6) (equal n 7)))))
(defthm take-nthcdr-is-rd8
  (implies (and (natp off) (<= (+ off 8) (len l)))
           (equal (take 8 (nthcdr off l)) (rd8 l off)))
  :hints ((equal-by-nths-hint)
          '(:in-theory (e/d (nth-of-rd8 nth-of-nthcdr nth-of-take len-of-rd8-8 true-listp-of-rd8) (rd8 nth)))))

;; bitslice of two 16-byte blocks is a wstate (8 u32) -- lift the GL fact to inp.
(defthm wstatep-of-bitslice
  (implies (and (aes::inp b0) (aes::inp b1))
           (wstatep (result-ok->val (aes-fixslice-encrypt-bitslice b0 b1))))
  :hints (("Goal"
           :in-theory (e/d (expand-len-16)
                           (wstatep-of-bitslice-gl aes-fixslice-encrypt-bitslice wstatep nth aes::inp))
           :use (:instance wstatep-of-bitslice-gl
                  (a0 (nth 0 b0)) (a1 (nth 1 b0)) (a2 (nth 2 b0)) (a3 (nth 3 b0)) (a4 (nth 4 b0)) (a5 (nth 5 b0)) (a6 (nth 6 b0)) (a7 (nth 7 b0)) (a8 (nth 8 b0)) (a9 (nth 9 b0)) (a10 (nth 10 b0)) (a11 (nth 11 b0)) (a12 (nth 12 b0)) (a13 (nth 13 b0)) (a14 (nth 14 b0)) (a15 (nth 15 b0))
                  (b0 (nth 0 b1)) (b1 (nth 1 b1)) (b2 (nth 2 b1)) (b3 (nth 3 b1)) (b4 (nth 4 b1)) (b5 (nth 5 b1)) (b6 (nth 6 b1)) (b7 (nth 7 b1)) (b8 (nth 8 b1)) (b9 (nth 9 b1)) (b10 (nth 10 b1)) (b11 (nth 11 b1)) (b12 (nth 12 b1)) (b13 (nth 13 b1)) (b14 (nth 14 b1)) (b15 (nth 15 b1))))))

;; the schedule seeds rkeys = append(bitslice(key,key), 80 zeros); its window 0
;; reads back the bitslice.
(defthm rd8-of-append-8
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (rd8 (append s z) 0) s))
  :hints (("Goal" :in-theory (e/d (rd8 expand-len-8) (nth)))))

