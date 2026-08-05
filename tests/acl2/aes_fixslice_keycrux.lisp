; Phase 4 -- key-schedule: bridges toward connecting krw8 to the spec recurrence.
;
; STATUS: the three BRIDGES below are proven and reusable --
;   take-nthcdr-is-rd8 : the keycore cruxes read the window as (take 8 (nthcdr
;                        off .)); that is our rd8 in bounds
;   wstatep-of-bitslice: bitslice of two inp blocks is a wstate (GL fact lifted)
;   rd8-of-append-8    : rd8 of the seed array reads back the bitslice
;
; The intended payoff -- krw8-crux-c : car(inv_bitslice(krw8(bitslice(b,b),c)))
; = kr-spec-bytes(b, xpow c) -- is NOT yet proven for any c.  It combines
; key-round-step-rcon{c} (keycore) with key-round-window (keyround) over the seed
; rk0 = append(bitslice(b,b), 80 zeros).  The window/take-nthcdr substitution
; lines up cleanly, but the step is tangled with lifting the GL crux's sixteen
; (unsigned-byte-p 8 (nth i b)) hypotheses to a single (aes::inp b): done in one
; shot the rewriter either blows up (~200s) or drowns in unsigned-byte-p case
; splits.  The fix is to SEPARATE the two: first lift the crux to (inp b) using
; this codebase's standard -general idiom (:use gl + expand-len-16 + disabled
; functions, as in subbytes/correspondence), then substitute the window against
; that clean c-general fact.  All the pieces (key-round-window, wstatep-of-
; bitslice, take-nthcdr-is-rd8, expand-len-16, unsigned-byte-p-8-of-nth-when-inp)
; are in place.
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

