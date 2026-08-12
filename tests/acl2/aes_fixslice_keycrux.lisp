; Phase 4 -- key-schedule crux: one key_round step == the AES key-expansion
; recurrence, lifted from the sixteen symbolic key bytes to ALL inputs.
;
; PROVEN HERE, for every 16-byte block b (i.e. (aes::inp b)):
;   krw8-crux-c  (c = 0..9):
;       car(inv_bitslice(krw8(bitslice(b,b), c))) = kr-spec-bytes(b, xpow_c)
;   where xpow = [1,2,4,8,16,32,64,128,27,54] is the AES round-constant column
;   and krw8 (defined in keyround) is the off-independent window transform one
;   key_round applies.  This connects the extracted fixslice key_round to
;   Kestrel's validated key-expansion recurrence kr-spec-bytes for ALL inputs
;   (the per-byte GL cruxes covered only the symbolic-byte form).
;
; HOW.  The keycore GL theorems key-round-step-rcon{c} establish the equality
; for the sixteen symbolic bytes a0..a15.  Each is (a) LIFTED to a single
; (aes::inp b) with this codebase's standard -general idiom: restate with the
; bytes explicit (crux{c}-bytes, via :use under ground-zero) then fold the
; byte-lists back to b with expand-len-16 + unsigned-byte-p-8-of-nth-when-inp
; (crux{c}-general); and (b) REPHRASED from the crux's window shape
; (take 8 (nthcdr 8 (cdr (key_round .)))) to krw8(bitslice(b,b),c) via the window
; equations window-eq-{c}, using take-nthcdr-is-rd8, key-round-window (keyround)
; and rd8-of-append-8 over the seed rk0 = append(bitslice(b,b), 80 zeros).  All
; big extracted functions stay closed -- every proof over them is pinned to
; (theory 'ground-zero) with explicit :use -- so nothing walks the huge bodies
; (a single-shot lift otherwise blows up ~200s in clausification).
;
; BRIDGES (proven first, reused throughout):
;   take-nthcdr-is-rd8 : the cruxes read the window as (take 8 (nthcdr off .));
;                        that is our rd8 in bounds
;   wstatep-of-bitslice: bitslice of two inp blocks is a wstate (GL fact lifted)
;   rd8-of-append-8    : rd8 of the seed array reads back the bitslice
;
; NEXT (not in this book): fold krw8-crux-c across the 10 concrete offsets
; (0,8,..,80) using key-round-window / key-round-frame-below / wstatep-of-krw8
; to get inv_bitslice(window r) = kk(r), r=0..10 -- the full key schedule.
(in-package "ACL2")
(include-book "aes_fixslice_keyround")
(include-book "aes_fixslice_keycore")
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/append" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))
(local (in-theory (disable nth-when-zp len-when-wstatep true-listp-when-wstatep)))

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
           (wstatep (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b0 b1))))
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


;; ===========================================================================
;; STEP 1 (per c): lift the keycore GL crux to (aes::inp b).
;; crux{c}-bytes restates key-round-step-rcon{c} with the sixteen bytes explicit
;; (identity via :use under ground-zero); crux{c}-general folds the byte-lists
;; back to b (expand-len-16 + unsigned-byte-p-8-of-nth-when-inp), all facts
;; supplied by :use so no enabled rule walks the extracted key_round body.
;; ===========================================================================
(defthm crux0-bytes
  (implies (and (unsigned-byte-p 8 (nth 0 b)) (unsigned-byte-p 8 (nth 1 b)) (unsigned-byte-p 8 (nth 2 b)) (unsigned-byte-p 8 (nth 3 b)) (unsigned-byte-p 8 (nth 4 b)) (unsigned-byte-p 8 (nth 5 b)) (unsigned-byte-p 8 (nth 6 b)) (unsigned-byte-p 8 (nth 7 b)) (unsigned-byte-p 8 (nth 8 b)) (unsigned-byte-p 8 (nth 9 b)) (unsigned-byte-p 8 (nth 10 b)) (unsigned-byte-p 8 (nth 11 b)) (unsigned-byte-p 8 (nth 12 b)) (unsigned-byte-p 8 (nth 13 b)) (unsigned-byte-p 8 (nth 14 b)) (unsigned-byte-p 8 (nth 15 b)))
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (take 8 (nthcdr 8 (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100
                                   (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0)
                                             (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b))
                                             (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b))))
                                           (make-list 80 :initial-element 0)) 0 0))))))))
                  (kr-spec-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) 1)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance key-round-step-rcon0
                   (a0 (nth 0 b)) (a1 (nth 1 b)) (a2 (nth 2 b)) (a3 (nth 3 b)) (a4 (nth 4 b)) (a5 (nth 5 b)) (a6 (nth 6 b)) (a7 (nth 7 b)) (a8 (nth 8 b)) (a9 (nth 9 b)) (a10 (nth 10 b)) (a11 (nth 11 b)) (a12 (nth 12 b)) (a13 (nth 13 b)) (a14 (nth 14 b)) (a15 (nth 15 b))))
           :in-theory (union-theories (theory 'ground-zero) '()))))

;; Lift crux0-bytes to (inp b): supply the 16 byte facts and the list-collapse
;; as explicit :use instances under ground-zero -- NO enabled rewrite rules, so
;; nothing walks the big term repeatedly.
(defthm crux0-general
  (implies (aes::inp b)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (take 8 (nthcdr 8 (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100
                                   (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                           (make-list 80 :initial-element 0)) 0 0))))))))
                  (kr-spec-bytes b 1)))
  :hints (("Goal" :do-not-induct t
           :use (crux0-bytes (:instance expand-len-16 (x b)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 0)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 1)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 2)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 3)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 4)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 5)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 6)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 7)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 8)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 9)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 10)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 11)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 12)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 13)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 14)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 15)))
           :in-theory (union-theories (theory 'ground-zero)
                                      '(true-listp-when-inp len-when-inp)))))

;; ===========================================================================
;; STEP 2: substitute the window against crux0-general.
;; crux0-general reads the new window as (take 8 (nthcdr 8 (cdr (key-round ...))));
;; we rewrite that window to krw8(bitslice(b,b),0) via take-nthcdr-is-rd8,
;; key-round-window, and rd8-of-append-8.  All big functions stay closed; the
;; supporting facts about rk0 = append(bitslice(b,b), 80 zeros) are proven as
;; small structured rewrites (no len-when-wstatep backchaining).
;; ---------------------------------------------------------------------------

;; W := (bitslice b b) is a wstate, hence true-listp and len 8.
(defthm wstate-bb
  (implies (aes::inp b)
           (wstatep (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))))
  :hints (("Goal" :use (:instance wstatep-of-bitslice (b0 b) (b1 b))
           :in-theory (theory 'ground-zero))))

(defthm len-bb
  (implies (aes::inp b)
           (equal (len (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))) 8))
  :hints (("Goal" :use (wstate-bb
                        (:instance len-when-wstatep
                          (x (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)))))
           :in-theory (theory 'ground-zero))))

(defthm tl-bb
  (implies (aes::inp b)
           (true-listp (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))))
  :hints (("Goal" :use (wstate-bb
                        (:instance true-listp-when-wstatep
                          (x (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)))))
           :in-theory (theory 'ground-zero))))

;; rk0 length and shape (bitslice closed).
(defthm len-rk0
  (implies (aes::inp b)
           (equal (len (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                               (make-list 80 :initial-element 0)))
                  88))
  :hints (("Goal" :use len-bb
           :in-theory (e/d (len-of-append)
                           (aes-fixslice-encrypt-bitslice)))))

(defthm tl-rk0
  (true-listp (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                      (make-list 80 :initial-element 0)))
  :hints (("Goal" :in-theory (e/d (true-listp-of-append)
                                  (aes-fixslice-encrypt-bitslice)))))

;; window 0 of rk0 reads back the bitslice.
(defthm rd8-rk0
  (implies (aes::inp b)
           (equal (rd8 (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                               (make-list 80 :initial-element 0)) 0)
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))))
  :hints (("Goal" :use (tl-bb len-bb
                        (:instance rd8-of-append-8
                          (s (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)))
                          (z (make-list 80 :initial-element 0))))
           :in-theory (disable aes-fixslice-encrypt-bitslice rd8))))

(defthm wstate-rd8-rk0
  (implies (aes::inp b)
           (wstatep (rd8 (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                 (make-list 80 :initial-element 0)) 0)))
  :hints (("Goal" :use (wstate-bb rd8-rk0)
           :in-theory (disable aes-fixslice-encrypt-bitslice rd8 wstatep))))

;; length of the key_round output (for the take-nthcdr bound).
(defthm len-cdr-kr0
  (implies (aes::inp b)
           (equal (len (cdr (result-ok->val
                     (aes-fixslice-encrypt-key-round 100
                       (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                               (make-list 80 :initial-element 0)) 0 0))))
                  88))
  :hints (("Goal" :do-not-induct t
           :use (len-rk0 tl-rk0 wstate-rd8-rk0
                        (:instance key-round-len
                          (rkeys (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                         (make-list 80 :initial-element 0)))
                          (off 0) (c 0)))
           :in-theory (theory 'ground-zero))))

;; the window read = krw8(bitslice(b,b),0).
(defthm window-eq-0
  (implies (aes::inp b)
           (equal (take 8 (nthcdr 8
                    (cdr (result-ok->val
                      (aes-fixslice-encrypt-key-round 100
                        (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                (make-list 80 :initial-element 0)) 0 0)))))
                  (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 0)))
  :hints (("Goal" :do-not-induct t
           :use (len-cdr-kr0 len-rk0 tl-rk0 wstate-rd8-rk0 rd8-rk0
                 (:instance take-nthcdr-is-rd8
                   (off 8)
                   (l (cdr (result-ok->val
                        (aes-fixslice-encrypt-key-round 100
                          (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                  (make-list 80 :initial-element 0)) 0 0)))))
                 (:instance key-round-window
                   (rkeys (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                  (make-list 80 :initial-element 0)))
                   (off 0) (c 0)))
           :in-theory (theory 'ground-zero))))

;; STEP 2 payoff: car(inv_bitslice(krw8(bitslice(b,b),0))) = kr-spec-bytes(b,1).
(defthm krw8-crux-0
  (implies (aes::inp b)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 0))))
                  (kr-spec-bytes b 1)))
  :hints (("Goal" :do-not-induct t
           :use (crux0-general window-eq-0)
           :in-theory (theory 'ground-zero))))

;; ===========================================================================
;; c = 1..9 : same lift + window substitution, one round constant each.
;; ===========================================================================
;; ---- c = 1 (rcon index 1, xpow 2) ----
(defthm crux1-bytes
  (implies (and (unsigned-byte-p 8 (nth 0 b)) (unsigned-byte-p 8 (nth 1 b)) (unsigned-byte-p 8 (nth 2 b)) (unsigned-byte-p 8 (nth 3 b)) (unsigned-byte-p 8 (nth 4 b)) (unsigned-byte-p 8 (nth 5 b)) (unsigned-byte-p 8 (nth 6 b)) (unsigned-byte-p 8 (nth 7 b)) (unsigned-byte-p 8 (nth 8 b)) (unsigned-byte-p 8 (nth 9 b)) (unsigned-byte-p 8 (nth 10 b)) (unsigned-byte-p 8 (nth 11 b)) (unsigned-byte-p 8 (nth 12 b)) (unsigned-byte-p 8 (nth 13 b)) (unsigned-byte-p 8 (nth 14 b)) (unsigned-byte-p 8 (nth 15 b)))
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (take 8 (nthcdr 8 (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100
                                   (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b))))
                                    (make-list 80 :initial-element 0)) 0 1))))))))
                  (kr-spec-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) 2)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance key-round-step-rcon1 (a0 (nth 0 b)) (a1 (nth 1 b)) (a2 (nth 2 b)) (a3 (nth 3 b)) (a4 (nth 4 b)) (a5 (nth 5 b)) (a6 (nth 6 b)) (a7 (nth 7 b)) (a8 (nth 8 b)) (a9 (nth 9 b)) (a10 (nth 10 b)) (a11 (nth 11 b)) (a12 (nth 12 b)) (a13 (nth 13 b)) (a14 (nth 14 b)) (a15 (nth 15 b))))
           :in-theory (union-theories (theory 'ground-zero) '()))))

(defthm crux1-general
  (implies (aes::inp b)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (take 8 (nthcdr 8 (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100
                                   (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)) 0 1))))))))
                  (kr-spec-bytes b 2)))
  :hints (("Goal" :do-not-induct t
           :use (crux1-bytes (:instance expand-len-16 (x b)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 0)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 1)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 2)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 3)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 4)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 5)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 6)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 7)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 8)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 9)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 10)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 11)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 12)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 13)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 14)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 15)))
           :in-theory (union-theories (theory 'ground-zero)
                                      '(true-listp-when-inp len-when-inp)))))

(defthm len-cdr-kr1
  (implies (aes::inp b)
           (equal (len (cdr (result-ok->val
                     (aes-fixslice-encrypt-key-round 100
                       (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)) 0 1))))
                  88))
  :hints (("Goal" :do-not-induct t
           :use (len-rk0 tl-rk0 wstate-rd8-rk0
                        (:instance key-round-len
                          (rkeys (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)))
                          (off 0) (c 1)))
           :in-theory (theory 'ground-zero))))

(defthm window-eq-1
  (implies (aes::inp b)
           (equal (take 8 (nthcdr 8
                    (cdr (result-ok->val
                      (aes-fixslice-encrypt-key-round 100
                        (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)) 0 1)))))
                  (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 1)))
  :hints (("Goal" :do-not-induct t
           :use (len-cdr-kr1 len-rk0 tl-rk0 wstate-rd8-rk0 rd8-rk0
                 (:instance take-nthcdr-is-rd8
                   (off 8)
                   (l (cdr (result-ok->val
                        (aes-fixslice-encrypt-key-round 100
                          (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)) 0 1)))))
                 (:instance key-round-window
                   (rkeys (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)))
                   (off 0) (c 1)))
           :in-theory (theory 'ground-zero))))

(defthm krw8-crux-1
  (implies (aes::inp b)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 1))))
                  (kr-spec-bytes b 2)))
  :hints (("Goal" :do-not-induct t
           :use (crux1-general window-eq-1)
           :in-theory (theory 'ground-zero))))

;; ---- c = 2 (rcon index 2, xpow 4) ----
(defthm crux2-bytes
  (implies (and (unsigned-byte-p 8 (nth 0 b)) (unsigned-byte-p 8 (nth 1 b)) (unsigned-byte-p 8 (nth 2 b)) (unsigned-byte-p 8 (nth 3 b)) (unsigned-byte-p 8 (nth 4 b)) (unsigned-byte-p 8 (nth 5 b)) (unsigned-byte-p 8 (nth 6 b)) (unsigned-byte-p 8 (nth 7 b)) (unsigned-byte-p 8 (nth 8 b)) (unsigned-byte-p 8 (nth 9 b)) (unsigned-byte-p 8 (nth 10 b)) (unsigned-byte-p 8 (nth 11 b)) (unsigned-byte-p 8 (nth 12 b)) (unsigned-byte-p 8 (nth 13 b)) (unsigned-byte-p 8 (nth 14 b)) (unsigned-byte-p 8 (nth 15 b)))
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (take 8 (nthcdr 8 (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100
                                   (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b))))
                                    (make-list 80 :initial-element 0)) 0 2))))))))
                  (kr-spec-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) 4)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance key-round-step-rcon2 (a0 (nth 0 b)) (a1 (nth 1 b)) (a2 (nth 2 b)) (a3 (nth 3 b)) (a4 (nth 4 b)) (a5 (nth 5 b)) (a6 (nth 6 b)) (a7 (nth 7 b)) (a8 (nth 8 b)) (a9 (nth 9 b)) (a10 (nth 10 b)) (a11 (nth 11 b)) (a12 (nth 12 b)) (a13 (nth 13 b)) (a14 (nth 14 b)) (a15 (nth 15 b))))
           :in-theory (union-theories (theory 'ground-zero) '()))))

(defthm crux2-general
  (implies (aes::inp b)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (take 8 (nthcdr 8 (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100
                                   (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)) 0 2))))))))
                  (kr-spec-bytes b 4)))
  :hints (("Goal" :do-not-induct t
           :use (crux2-bytes (:instance expand-len-16 (x b)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 0)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 1)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 2)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 3)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 4)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 5)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 6)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 7)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 8)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 9)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 10)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 11)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 12)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 13)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 14)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 15)))
           :in-theory (union-theories (theory 'ground-zero)
                                      '(true-listp-when-inp len-when-inp)))))

(defthm len-cdr-kr2
  (implies (aes::inp b)
           (equal (len (cdr (result-ok->val
                     (aes-fixslice-encrypt-key-round 100
                       (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)) 0 2))))
                  88))
  :hints (("Goal" :do-not-induct t
           :use (len-rk0 tl-rk0 wstate-rd8-rk0
                        (:instance key-round-len
                          (rkeys (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)))
                          (off 0) (c 2)))
           :in-theory (theory 'ground-zero))))

(defthm window-eq-2
  (implies (aes::inp b)
           (equal (take 8 (nthcdr 8
                    (cdr (result-ok->val
                      (aes-fixslice-encrypt-key-round 100
                        (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)) 0 2)))))
                  (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 2)))
  :hints (("Goal" :do-not-induct t
           :use (len-cdr-kr2 len-rk0 tl-rk0 wstate-rd8-rk0 rd8-rk0
                 (:instance take-nthcdr-is-rd8
                   (off 8)
                   (l (cdr (result-ok->val
                        (aes-fixslice-encrypt-key-round 100
                          (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)) 0 2)))))
                 (:instance key-round-window
                   (rkeys (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)))
                   (off 0) (c 2)))
           :in-theory (theory 'ground-zero))))

(defthm krw8-crux-2
  (implies (aes::inp b)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 2))))
                  (kr-spec-bytes b 4)))
  :hints (("Goal" :do-not-induct t
           :use (crux2-general window-eq-2)
           :in-theory (theory 'ground-zero))))

;; ---- c = 3 (rcon index 3, xpow 8) ----
(defthm crux3-bytes
  (implies (and (unsigned-byte-p 8 (nth 0 b)) (unsigned-byte-p 8 (nth 1 b)) (unsigned-byte-p 8 (nth 2 b)) (unsigned-byte-p 8 (nth 3 b)) (unsigned-byte-p 8 (nth 4 b)) (unsigned-byte-p 8 (nth 5 b)) (unsigned-byte-p 8 (nth 6 b)) (unsigned-byte-p 8 (nth 7 b)) (unsigned-byte-p 8 (nth 8 b)) (unsigned-byte-p 8 (nth 9 b)) (unsigned-byte-p 8 (nth 10 b)) (unsigned-byte-p 8 (nth 11 b)) (unsigned-byte-p 8 (nth 12 b)) (unsigned-byte-p 8 (nth 13 b)) (unsigned-byte-p 8 (nth 14 b)) (unsigned-byte-p 8 (nth 15 b)))
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (take 8 (nthcdr 8 (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100
                                   (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b))))
                                    (make-list 80 :initial-element 0)) 0 3))))))))
                  (kr-spec-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) 8)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance key-round-step-rcon3 (a0 (nth 0 b)) (a1 (nth 1 b)) (a2 (nth 2 b)) (a3 (nth 3 b)) (a4 (nth 4 b)) (a5 (nth 5 b)) (a6 (nth 6 b)) (a7 (nth 7 b)) (a8 (nth 8 b)) (a9 (nth 9 b)) (a10 (nth 10 b)) (a11 (nth 11 b)) (a12 (nth 12 b)) (a13 (nth 13 b)) (a14 (nth 14 b)) (a15 (nth 15 b))))
           :in-theory (union-theories (theory 'ground-zero) '()))))

(defthm crux3-general
  (implies (aes::inp b)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (take 8 (nthcdr 8 (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100
                                   (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)) 0 3))))))))
                  (kr-spec-bytes b 8)))
  :hints (("Goal" :do-not-induct t
           :use (crux3-bytes (:instance expand-len-16 (x b)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 0)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 1)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 2)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 3)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 4)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 5)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 6)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 7)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 8)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 9)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 10)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 11)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 12)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 13)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 14)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 15)))
           :in-theory (union-theories (theory 'ground-zero)
                                      '(true-listp-when-inp len-when-inp)))))

(defthm len-cdr-kr3
  (implies (aes::inp b)
           (equal (len (cdr (result-ok->val
                     (aes-fixslice-encrypt-key-round 100
                       (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)) 0 3))))
                  88))
  :hints (("Goal" :do-not-induct t
           :use (len-rk0 tl-rk0 wstate-rd8-rk0
                        (:instance key-round-len
                          (rkeys (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)))
                          (off 0) (c 3)))
           :in-theory (theory 'ground-zero))))

(defthm window-eq-3
  (implies (aes::inp b)
           (equal (take 8 (nthcdr 8
                    (cdr (result-ok->val
                      (aes-fixslice-encrypt-key-round 100
                        (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)) 0 3)))))
                  (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 3)))
  :hints (("Goal" :do-not-induct t
           :use (len-cdr-kr3 len-rk0 tl-rk0 wstate-rd8-rk0 rd8-rk0
                 (:instance take-nthcdr-is-rd8
                   (off 8)
                   (l (cdr (result-ok->val
                        (aes-fixslice-encrypt-key-round 100
                          (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)) 0 3)))))
                 (:instance key-round-window
                   (rkeys (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)))
                   (off 0) (c 3)))
           :in-theory (theory 'ground-zero))))

(defthm krw8-crux-3
  (implies (aes::inp b)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 3))))
                  (kr-spec-bytes b 8)))
  :hints (("Goal" :do-not-induct t
           :use (crux3-general window-eq-3)
           :in-theory (theory 'ground-zero))))

;; ---- c = 4 (rcon index 4, xpow 16) ----
(defthm crux4-bytes
  (implies (and (unsigned-byte-p 8 (nth 0 b)) (unsigned-byte-p 8 (nth 1 b)) (unsigned-byte-p 8 (nth 2 b)) (unsigned-byte-p 8 (nth 3 b)) (unsigned-byte-p 8 (nth 4 b)) (unsigned-byte-p 8 (nth 5 b)) (unsigned-byte-p 8 (nth 6 b)) (unsigned-byte-p 8 (nth 7 b)) (unsigned-byte-p 8 (nth 8 b)) (unsigned-byte-p 8 (nth 9 b)) (unsigned-byte-p 8 (nth 10 b)) (unsigned-byte-p 8 (nth 11 b)) (unsigned-byte-p 8 (nth 12 b)) (unsigned-byte-p 8 (nth 13 b)) (unsigned-byte-p 8 (nth 14 b)) (unsigned-byte-p 8 (nth 15 b)))
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (take 8 (nthcdr 8 (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100
                                   (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b))))
                                    (make-list 80 :initial-element 0)) 0 4))))))))
                  (kr-spec-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) 16)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance key-round-step-rcon4 (a0 (nth 0 b)) (a1 (nth 1 b)) (a2 (nth 2 b)) (a3 (nth 3 b)) (a4 (nth 4 b)) (a5 (nth 5 b)) (a6 (nth 6 b)) (a7 (nth 7 b)) (a8 (nth 8 b)) (a9 (nth 9 b)) (a10 (nth 10 b)) (a11 (nth 11 b)) (a12 (nth 12 b)) (a13 (nth 13 b)) (a14 (nth 14 b)) (a15 (nth 15 b))))
           :in-theory (union-theories (theory 'ground-zero) '()))))

(defthm crux4-general
  (implies (aes::inp b)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (take 8 (nthcdr 8 (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100
                                   (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)) 0 4))))))))
                  (kr-spec-bytes b 16)))
  :hints (("Goal" :do-not-induct t
           :use (crux4-bytes (:instance expand-len-16 (x b)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 0)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 1)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 2)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 3)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 4)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 5)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 6)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 7)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 8)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 9)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 10)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 11)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 12)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 13)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 14)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 15)))
           :in-theory (union-theories (theory 'ground-zero)
                                      '(true-listp-when-inp len-when-inp)))))

(defthm len-cdr-kr4
  (implies (aes::inp b)
           (equal (len (cdr (result-ok->val
                     (aes-fixslice-encrypt-key-round 100
                       (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)) 0 4))))
                  88))
  :hints (("Goal" :do-not-induct t
           :use (len-rk0 tl-rk0 wstate-rd8-rk0
                        (:instance key-round-len
                          (rkeys (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)))
                          (off 0) (c 4)))
           :in-theory (theory 'ground-zero))))

(defthm window-eq-4
  (implies (aes::inp b)
           (equal (take 8 (nthcdr 8
                    (cdr (result-ok->val
                      (aes-fixslice-encrypt-key-round 100
                        (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)) 0 4)))))
                  (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 4)))
  :hints (("Goal" :do-not-induct t
           :use (len-cdr-kr4 len-rk0 tl-rk0 wstate-rd8-rk0 rd8-rk0
                 (:instance take-nthcdr-is-rd8
                   (off 8)
                   (l (cdr (result-ok->val
                        (aes-fixslice-encrypt-key-round 100
                          (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)) 0 4)))))
                 (:instance key-round-window
                   (rkeys (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)))
                   (off 0) (c 4)))
           :in-theory (theory 'ground-zero))))

(defthm krw8-crux-4
  (implies (aes::inp b)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 4))))
                  (kr-spec-bytes b 16)))
  :hints (("Goal" :do-not-induct t
           :use (crux4-general window-eq-4)
           :in-theory (theory 'ground-zero))))

;; ---- c = 5 (rcon index 5, xpow 32) ----
(defthm crux5-bytes
  (implies (and (unsigned-byte-p 8 (nth 0 b)) (unsigned-byte-p 8 (nth 1 b)) (unsigned-byte-p 8 (nth 2 b)) (unsigned-byte-p 8 (nth 3 b)) (unsigned-byte-p 8 (nth 4 b)) (unsigned-byte-p 8 (nth 5 b)) (unsigned-byte-p 8 (nth 6 b)) (unsigned-byte-p 8 (nth 7 b)) (unsigned-byte-p 8 (nth 8 b)) (unsigned-byte-p 8 (nth 9 b)) (unsigned-byte-p 8 (nth 10 b)) (unsigned-byte-p 8 (nth 11 b)) (unsigned-byte-p 8 (nth 12 b)) (unsigned-byte-p 8 (nth 13 b)) (unsigned-byte-p 8 (nth 14 b)) (unsigned-byte-p 8 (nth 15 b)))
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (take 8 (nthcdr 8 (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100
                                   (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b))))
                                    (make-list 80 :initial-element 0)) 0 5))))))))
                  (kr-spec-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) 32)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance key-round-step-rcon5 (a0 (nth 0 b)) (a1 (nth 1 b)) (a2 (nth 2 b)) (a3 (nth 3 b)) (a4 (nth 4 b)) (a5 (nth 5 b)) (a6 (nth 6 b)) (a7 (nth 7 b)) (a8 (nth 8 b)) (a9 (nth 9 b)) (a10 (nth 10 b)) (a11 (nth 11 b)) (a12 (nth 12 b)) (a13 (nth 13 b)) (a14 (nth 14 b)) (a15 (nth 15 b))))
           :in-theory (union-theories (theory 'ground-zero) '()))))

(defthm crux5-general
  (implies (aes::inp b)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (take 8 (nthcdr 8 (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100
                                   (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)) 0 5))))))))
                  (kr-spec-bytes b 32)))
  :hints (("Goal" :do-not-induct t
           :use (crux5-bytes (:instance expand-len-16 (x b)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 0)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 1)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 2)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 3)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 4)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 5)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 6)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 7)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 8)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 9)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 10)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 11)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 12)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 13)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 14)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 15)))
           :in-theory (union-theories (theory 'ground-zero)
                                      '(true-listp-when-inp len-when-inp)))))

(defthm len-cdr-kr5
  (implies (aes::inp b)
           (equal (len (cdr (result-ok->val
                     (aes-fixslice-encrypt-key-round 100
                       (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)) 0 5))))
                  88))
  :hints (("Goal" :do-not-induct t
           :use (len-rk0 tl-rk0 wstate-rd8-rk0
                        (:instance key-round-len
                          (rkeys (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)))
                          (off 0) (c 5)))
           :in-theory (theory 'ground-zero))))

(defthm window-eq-5
  (implies (aes::inp b)
           (equal (take 8 (nthcdr 8
                    (cdr (result-ok->val
                      (aes-fixslice-encrypt-key-round 100
                        (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)) 0 5)))))
                  (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 5)))
  :hints (("Goal" :do-not-induct t
           :use (len-cdr-kr5 len-rk0 tl-rk0 wstate-rd8-rk0 rd8-rk0
                 (:instance take-nthcdr-is-rd8
                   (off 8)
                   (l (cdr (result-ok->val
                        (aes-fixslice-encrypt-key-round 100
                          (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)) 0 5)))))
                 (:instance key-round-window
                   (rkeys (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)))
                   (off 0) (c 5)))
           :in-theory (theory 'ground-zero))))

(defthm krw8-crux-5
  (implies (aes::inp b)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 5))))
                  (kr-spec-bytes b 32)))
  :hints (("Goal" :do-not-induct t
           :use (crux5-general window-eq-5)
           :in-theory (theory 'ground-zero))))

;; ---- c = 6 (rcon index 6, xpow 64) ----
(defthm crux6-bytes
  (implies (and (unsigned-byte-p 8 (nth 0 b)) (unsigned-byte-p 8 (nth 1 b)) (unsigned-byte-p 8 (nth 2 b)) (unsigned-byte-p 8 (nth 3 b)) (unsigned-byte-p 8 (nth 4 b)) (unsigned-byte-p 8 (nth 5 b)) (unsigned-byte-p 8 (nth 6 b)) (unsigned-byte-p 8 (nth 7 b)) (unsigned-byte-p 8 (nth 8 b)) (unsigned-byte-p 8 (nth 9 b)) (unsigned-byte-p 8 (nth 10 b)) (unsigned-byte-p 8 (nth 11 b)) (unsigned-byte-p 8 (nth 12 b)) (unsigned-byte-p 8 (nth 13 b)) (unsigned-byte-p 8 (nth 14 b)) (unsigned-byte-p 8 (nth 15 b)))
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (take 8 (nthcdr 8 (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100
                                   (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b))))
                                    (make-list 80 :initial-element 0)) 0 6))))))))
                  (kr-spec-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) 64)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance key-round-step-rcon6 (a0 (nth 0 b)) (a1 (nth 1 b)) (a2 (nth 2 b)) (a3 (nth 3 b)) (a4 (nth 4 b)) (a5 (nth 5 b)) (a6 (nth 6 b)) (a7 (nth 7 b)) (a8 (nth 8 b)) (a9 (nth 9 b)) (a10 (nth 10 b)) (a11 (nth 11 b)) (a12 (nth 12 b)) (a13 (nth 13 b)) (a14 (nth 14 b)) (a15 (nth 15 b))))
           :in-theory (union-theories (theory 'ground-zero) '()))))

(defthm crux6-general
  (implies (aes::inp b)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (take 8 (nthcdr 8 (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100
                                   (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)) 0 6))))))))
                  (kr-spec-bytes b 64)))
  :hints (("Goal" :do-not-induct t
           :use (crux6-bytes (:instance expand-len-16 (x b)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 0)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 1)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 2)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 3)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 4)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 5)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 6)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 7)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 8)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 9)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 10)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 11)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 12)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 13)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 14)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 15)))
           :in-theory (union-theories (theory 'ground-zero)
                                      '(true-listp-when-inp len-when-inp)))))

(defthm len-cdr-kr6
  (implies (aes::inp b)
           (equal (len (cdr (result-ok->val
                     (aes-fixslice-encrypt-key-round 100
                       (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)) 0 6))))
                  88))
  :hints (("Goal" :do-not-induct t
           :use (len-rk0 tl-rk0 wstate-rd8-rk0
                        (:instance key-round-len
                          (rkeys (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)))
                          (off 0) (c 6)))
           :in-theory (theory 'ground-zero))))

(defthm window-eq-6
  (implies (aes::inp b)
           (equal (take 8 (nthcdr 8
                    (cdr (result-ok->val
                      (aes-fixslice-encrypt-key-round 100
                        (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)) 0 6)))))
                  (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 6)))
  :hints (("Goal" :do-not-induct t
           :use (len-cdr-kr6 len-rk0 tl-rk0 wstate-rd8-rk0 rd8-rk0
                 (:instance take-nthcdr-is-rd8
                   (off 8)
                   (l (cdr (result-ok->val
                        (aes-fixslice-encrypt-key-round 100
                          (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)) 0 6)))))
                 (:instance key-round-window
                   (rkeys (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)))
                   (off 0) (c 6)))
           :in-theory (theory 'ground-zero))))

(defthm krw8-crux-6
  (implies (aes::inp b)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 6))))
                  (kr-spec-bytes b 64)))
  :hints (("Goal" :do-not-induct t
           :use (crux6-general window-eq-6)
           :in-theory (theory 'ground-zero))))

;; ---- c = 7 (rcon index 7, xpow 128) ----
(defthm crux7-bytes
  (implies (and (unsigned-byte-p 8 (nth 0 b)) (unsigned-byte-p 8 (nth 1 b)) (unsigned-byte-p 8 (nth 2 b)) (unsigned-byte-p 8 (nth 3 b)) (unsigned-byte-p 8 (nth 4 b)) (unsigned-byte-p 8 (nth 5 b)) (unsigned-byte-p 8 (nth 6 b)) (unsigned-byte-p 8 (nth 7 b)) (unsigned-byte-p 8 (nth 8 b)) (unsigned-byte-p 8 (nth 9 b)) (unsigned-byte-p 8 (nth 10 b)) (unsigned-byte-p 8 (nth 11 b)) (unsigned-byte-p 8 (nth 12 b)) (unsigned-byte-p 8 (nth 13 b)) (unsigned-byte-p 8 (nth 14 b)) (unsigned-byte-p 8 (nth 15 b)))
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (take 8 (nthcdr 8 (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100
                                   (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b))))
                                    (make-list 80 :initial-element 0)) 0 7))))))))
                  (kr-spec-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) 128)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance key-round-step-rcon7 (a0 (nth 0 b)) (a1 (nth 1 b)) (a2 (nth 2 b)) (a3 (nth 3 b)) (a4 (nth 4 b)) (a5 (nth 5 b)) (a6 (nth 6 b)) (a7 (nth 7 b)) (a8 (nth 8 b)) (a9 (nth 9 b)) (a10 (nth 10 b)) (a11 (nth 11 b)) (a12 (nth 12 b)) (a13 (nth 13 b)) (a14 (nth 14 b)) (a15 (nth 15 b))))
           :in-theory (union-theories (theory 'ground-zero) '()))))

(defthm crux7-general
  (implies (aes::inp b)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (take 8 (nthcdr 8 (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100
                                   (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)) 0 7))))))))
                  (kr-spec-bytes b 128)))
  :hints (("Goal" :do-not-induct t
           :use (crux7-bytes (:instance expand-len-16 (x b)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 0)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 1)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 2)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 3)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 4)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 5)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 6)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 7)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 8)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 9)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 10)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 11)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 12)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 13)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 14)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 15)))
           :in-theory (union-theories (theory 'ground-zero)
                                      '(true-listp-when-inp len-when-inp)))))

(defthm len-cdr-kr7
  (implies (aes::inp b)
           (equal (len (cdr (result-ok->val
                     (aes-fixslice-encrypt-key-round 100
                       (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)) 0 7))))
                  88))
  :hints (("Goal" :do-not-induct t
           :use (len-rk0 tl-rk0 wstate-rd8-rk0
                        (:instance key-round-len
                          (rkeys (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)))
                          (off 0) (c 7)))
           :in-theory (theory 'ground-zero))))

(defthm window-eq-7
  (implies (aes::inp b)
           (equal (take 8 (nthcdr 8
                    (cdr (result-ok->val
                      (aes-fixslice-encrypt-key-round 100
                        (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)) 0 7)))))
                  (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 7)))
  :hints (("Goal" :do-not-induct t
           :use (len-cdr-kr7 len-rk0 tl-rk0 wstate-rd8-rk0 rd8-rk0
                 (:instance take-nthcdr-is-rd8
                   (off 8)
                   (l (cdr (result-ok->val
                        (aes-fixslice-encrypt-key-round 100
                          (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)) 0 7)))))
                 (:instance key-round-window
                   (rkeys (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)))
                   (off 0) (c 7)))
           :in-theory (theory 'ground-zero))))

(defthm krw8-crux-7
  (implies (aes::inp b)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 7))))
                  (kr-spec-bytes b 128)))
  :hints (("Goal" :do-not-induct t
           :use (crux7-general window-eq-7)
           :in-theory (theory 'ground-zero))))

;; ---- c = 8 (rcon index 8, xpow 27) ----
(defthm crux8-bytes
  (implies (and (unsigned-byte-p 8 (nth 0 b)) (unsigned-byte-p 8 (nth 1 b)) (unsigned-byte-p 8 (nth 2 b)) (unsigned-byte-p 8 (nth 3 b)) (unsigned-byte-p 8 (nth 4 b)) (unsigned-byte-p 8 (nth 5 b)) (unsigned-byte-p 8 (nth 6 b)) (unsigned-byte-p 8 (nth 7 b)) (unsigned-byte-p 8 (nth 8 b)) (unsigned-byte-p 8 (nth 9 b)) (unsigned-byte-p 8 (nth 10 b)) (unsigned-byte-p 8 (nth 11 b)) (unsigned-byte-p 8 (nth 12 b)) (unsigned-byte-p 8 (nth 13 b)) (unsigned-byte-p 8 (nth 14 b)) (unsigned-byte-p 8 (nth 15 b)))
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (take 8 (nthcdr 8 (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100
                                   (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b))))
                                    (make-list 80 :initial-element 0)) 0 8))))))))
                  (kr-spec-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) 27)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance key-round-step-rcon8 (a0 (nth 0 b)) (a1 (nth 1 b)) (a2 (nth 2 b)) (a3 (nth 3 b)) (a4 (nth 4 b)) (a5 (nth 5 b)) (a6 (nth 6 b)) (a7 (nth 7 b)) (a8 (nth 8 b)) (a9 (nth 9 b)) (a10 (nth 10 b)) (a11 (nth 11 b)) (a12 (nth 12 b)) (a13 (nth 13 b)) (a14 (nth 14 b)) (a15 (nth 15 b))))
           :in-theory (union-theories (theory 'ground-zero) '()))))

(defthm crux8-general
  (implies (aes::inp b)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (take 8 (nthcdr 8 (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100
                                   (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)) 0 8))))))))
                  (kr-spec-bytes b 27)))
  :hints (("Goal" :do-not-induct t
           :use (crux8-bytes (:instance expand-len-16 (x b)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 0)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 1)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 2)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 3)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 4)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 5)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 6)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 7)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 8)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 9)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 10)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 11)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 12)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 13)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 14)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 15)))
           :in-theory (union-theories (theory 'ground-zero)
                                      '(true-listp-when-inp len-when-inp)))))

(defthm len-cdr-kr8
  (implies (aes::inp b)
           (equal (len (cdr (result-ok->val
                     (aes-fixslice-encrypt-key-round 100
                       (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)) 0 8))))
                  88))
  :hints (("Goal" :do-not-induct t
           :use (len-rk0 tl-rk0 wstate-rd8-rk0
                        (:instance key-round-len
                          (rkeys (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)))
                          (off 0) (c 8)))
           :in-theory (theory 'ground-zero))))

(defthm window-eq-8
  (implies (aes::inp b)
           (equal (take 8 (nthcdr 8
                    (cdr (result-ok->val
                      (aes-fixslice-encrypt-key-round 100
                        (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)) 0 8)))))
                  (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 8)))
  :hints (("Goal" :do-not-induct t
           :use (len-cdr-kr8 len-rk0 tl-rk0 wstate-rd8-rk0 rd8-rk0
                 (:instance take-nthcdr-is-rd8
                   (off 8)
                   (l (cdr (result-ok->val
                        (aes-fixslice-encrypt-key-round 100
                          (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)) 0 8)))))
                 (:instance key-round-window
                   (rkeys (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)))
                   (off 0) (c 8)))
           :in-theory (theory 'ground-zero))))

(defthm krw8-crux-8
  (implies (aes::inp b)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 8))))
                  (kr-spec-bytes b 27)))
  :hints (("Goal" :do-not-induct t
           :use (crux8-general window-eq-8)
           :in-theory (theory 'ground-zero))))

;; ---- c = 9 (rcon index 9, xpow 54) ----
(defthm crux9-bytes
  (implies (and (unsigned-byte-p 8 (nth 0 b)) (unsigned-byte-p 8 (nth 1 b)) (unsigned-byte-p 8 (nth 2 b)) (unsigned-byte-p 8 (nth 3 b)) (unsigned-byte-p 8 (nth 4 b)) (unsigned-byte-p 8 (nth 5 b)) (unsigned-byte-p 8 (nth 6 b)) (unsigned-byte-p 8 (nth 7 b)) (unsigned-byte-p 8 (nth 8 b)) (unsigned-byte-p 8 (nth 9 b)) (unsigned-byte-p 8 (nth 10 b)) (unsigned-byte-p 8 (nth 11 b)) (unsigned-byte-p 8 (nth 12 b)) (unsigned-byte-p 8 (nth 13 b)) (unsigned-byte-p 8 (nth 14 b)) (unsigned-byte-p 8 (nth 15 b)))
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (take 8 (nthcdr 8 (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100
                                   (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b))))
                                    (make-list 80 :initial-element 0)) 0 9))))))))
                  (kr-spec-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) 54)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance key-round-step-rcon9 (a0 (nth 0 b)) (a1 (nth 1 b)) (a2 (nth 2 b)) (a3 (nth 3 b)) (a4 (nth 4 b)) (a5 (nth 5 b)) (a6 (nth 6 b)) (a7 (nth 7 b)) (a8 (nth 8 b)) (a9 (nth 9 b)) (a10 (nth 10 b)) (a11 (nth 11 b)) (a12 (nth 12 b)) (a13 (nth 13 b)) (a14 (nth 14 b)) (a15 (nth 15 b))))
           :in-theory (union-theories (theory 'ground-zero) '()))))

(defthm crux9-general
  (implies (aes::inp b)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (take 8 (nthcdr 8 (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100
                                   (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)) 0 9))))))))
                  (kr-spec-bytes b 54)))
  :hints (("Goal" :do-not-induct t
           :use (crux9-bytes (:instance expand-len-16 (x b)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 0)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 1)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 2)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 3)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 4)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 5)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 6)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 7)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 8)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 9)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 10)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 11)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 12)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 13)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 14)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 15)))
           :in-theory (union-theories (theory 'ground-zero)
                                      '(true-listp-when-inp len-when-inp)))))

(defthm len-cdr-kr9
  (implies (aes::inp b)
           (equal (len (cdr (result-ok->val
                     (aes-fixslice-encrypt-key-round 100
                       (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)) 0 9))))
                  88))
  :hints (("Goal" :do-not-induct t
           :use (len-rk0 tl-rk0 wstate-rd8-rk0
                        (:instance key-round-len
                          (rkeys (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)))
                          (off 0) (c 9)))
           :in-theory (theory 'ground-zero))))

(defthm window-eq-9
  (implies (aes::inp b)
           (equal (take 8 (nthcdr 8
                    (cdr (result-ok->val
                      (aes-fixslice-encrypt-key-round 100
                        (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)) 0 9)))))
                  (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 9)))
  :hints (("Goal" :do-not-induct t
           :use (len-cdr-kr9 len-rk0 tl-rk0 wstate-rd8-rk0 rd8-rk0
                 (:instance take-nthcdr-is-rd8
                   (off 8)
                   (l (cdr (result-ok->val
                        (aes-fixslice-encrypt-key-round 100
                          (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)) 0 9)))))
                 (:instance key-round-window
                   (rkeys (append (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                                    (make-list 80 :initial-element 0)))
                   (off 0) (c 9)))
           :in-theory (theory 'ground-zero))))

(defthm krw8-crux-9
  (implies (aes::inp b)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 9))))
                  (kr-spec-bytes b 54)))
  :hints (("Goal" :do-not-induct t
           :use (crux9-general window-eq-9)
           :in-theory (theory 'ground-zero))))

