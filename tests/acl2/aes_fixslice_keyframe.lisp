; Phase 4 -- key schedule frame plumbing.
;
; Isolated into its own book so that arithmetic-5 stays LOCAL here: the rd8
; index reasoning below wants arithmetic-5, but arithmetic-5's aggressive
; subtraction/nonlinear case splits explode the wok inductions in keyexpand.
; Keeping it local means keyexpand can run the offset inductions on plain
; ground-zero linear arithmetic.
;
; Proven here (all for a key_round at offset off, given the standard window
; hypotheses):
;   true-listp-of-xc-spec / -cdr-key-round : the array stays a true-list
;   rd8-of-key-round-below : an 8-word read at or below off is unchanged
(in-package "ACL2")
(include-book "aes_fixslice_keystep")
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))
(local (in-theory (disable len-when-wstatep true-listp-when-wstatep)))

(defthm true-listp-of-xc-spec
  (implies (true-listp rkeys) (true-listp (xc-spec i e rkeys off dx dror)))
  :hints (("Goal" :induct (xc-spec i e rkeys off dx dror)
           :in-theory (disable xc-word))))

(defthm true-listp-of-cdr-key-round
  (implies (and (natp off) (equal (rem off 8) 0)
                (<= (+ off 16) (len rkeys)) (< (len rkeys) 4294967296)
                (true-listp rkeys) (wstatep (rd8 rkeys off)) (natp c) (< c 12))
           (true-listp (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100 rkeys off c)))))
  :hints (("Goal" :use key-round-unfold
           :in-theory (disable w8-spec ms-spec xc-spec nth arc-list
                               aes-fixslice-encrypt-key-round
                               aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-sub-bytes-nots))))

;; An 8-word read at offset k8 <= off is untouched by a key_round at off (which
;; writes only [off+8, off+16)).  Proven by nths + key-round-frame-below.
(defthm rd8-of-key-round-below
  (implies (and (natp off) (equal (rem off 8) 0)
                (<= (+ off 16) (len rkeys)) (< (len rkeys) 4294967296)
                (true-listp rkeys) (wstatep (rd8 rkeys off)) (natp c) (< c 12)
                (natp k8) (<= k8 off))
           (equal (rd8 (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100 rkeys off c))) k8)
                  (rd8 rkeys k8)))
  :hints ((equal-by-nths-hint)
          '(:in-theory (e/d (nth-of-rd8) (rd8 nth aes-fixslice-encrypt-key-round)))))
