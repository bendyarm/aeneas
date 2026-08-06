; Phase 4 -- key-schedule assembly: fold at-op infrastructure.
;
; The fold applies inv_shift_rows_{1,2,3} and sub_bytes_nots "at" a window offset
; (read8 ; op ; write8).  keyops already has sub-bytes-nots-at-is (= w8-spec);
; here we add the inv_shift_rows_i analogues, which need wstatep-of-inv-shift-
; rows-i (each is an alias for shift_rows_{3,2,1}, a wstate permutation -- proved
; by GL over the 8 u32 words, as wstatep-of-sub-bytes-nots is).
(in-package "ACL2")
(include-book "aes_fixslice_keyfold")
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))
;; nth-when-zp rewrites (nth 0 s) -> (car s), which blocks the expand-len-8
;; fold ((list (nth 0 s) ... (nth 7 s)) -> s) that lifts the GL struct facts.
(local (in-theory (disable len-when-wstatep true-listp-when-wstatep nth-when-zp)))

;; ---- inv_shift_rows_1: wstate permutation, and its at-op = w8-spec ----
(gl::def-gl-thm isr1-struct-gl
  :hyp (and (unsigned-byte-p 32 w0) (unsigned-byte-p 32 w1) (unsigned-byte-p 32 w2) (unsigned-byte-p 32 w3) (unsigned-byte-p 32 w4) (unsigned-byte-p 32 w5) (unsigned-byte-p 32 w6) (unsigned-byte-p 32 w7))
  :concl (and (equal (result-kind (aes-fixslice-encrypt-inv-shift-rows-1 100 (list w0 w1 w2 w3 w4 w5 w6 w7))) :ok)
              (wstatep (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1 100 (list w0 w1 w2 w3 w4 w5 w6 w7)))))
  :g-bindings (gl::auto-bindings (:nat w0 32) (:nat w1 32) (:nat w2 32) (:nat w3 32) (:nat w4 32) (:nat w5 32) (:nat w6 32) (:nat w7 32)))

(defthm result-kind-of-isr1
  (implies (wstatep s) (equal (result-kind (aes-fixslice-encrypt-inv-shift-rows-1 100 s)) :ok))
  :hints (("Goal" :in-theory (e/d (expand-len-8 wstatep) (isr1-struct-gl aes-fixslice-encrypt-inv-shift-rows-1 nth))
           :use (:instance isr1-struct-gl (w0 (nth 0 s)) (w1 (nth 1 s)) (w2 (nth 2 s)) (w3 (nth 3 s)) (w4 (nth 4 s)) (w5 (nth 5 s)) (w6 (nth 6 s)) (w7 (nth 7 s))))))

(defthm wstatep-of-isr1
  (implies (wstatep s) (wstatep (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1 100 s))))
  :hints (("Goal" :in-theory (e/d (expand-len-8 wstatep) (isr1-struct-gl aes-fixslice-encrypt-inv-shift-rows-1 nth))
           :use (:instance isr1-struct-gl (w0 (nth 0 s)) (w1 (nth 1 s)) (w2 (nth 2 s)) (w3 (nth 3 s)) (w4 (nth 4 s)) (w5 (nth 5 s)) (w6 (nth 6 s)) (w7 (nth 7 s))))))

(defthm inv-shift-rows-1-at-is
  (implies (and (natp off) (<= (+ off 8) (len rkeys)) (< (len rkeys) 4294967296)
                (wstatep (rd8 rkeys off)))
           (equal (aes-fixslice-encrypt-inv-shift-rows-1-at 100 rkeys off)
                  (ok (w8-spec 0 8 rkeys off
                        (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1 100 (rd8 rkeys off)))))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-1-at len-when-wstatep true-listp-when-wstatep) (aes-fixslice-encrypt-inv-shift-rows-1 w8-spec rd8 nth)))))

;; ---- inv_shift_rows_2: wstate permutation, and its at-op = w8-spec ----
(gl::def-gl-thm isr2-struct-gl
  :hyp (and (unsigned-byte-p 32 w0) (unsigned-byte-p 32 w1) (unsigned-byte-p 32 w2) (unsigned-byte-p 32 w3) (unsigned-byte-p 32 w4) (unsigned-byte-p 32 w5) (unsigned-byte-p 32 w6) (unsigned-byte-p 32 w7))
  :concl (and (equal (result-kind (aes-fixslice-encrypt-inv-shift-rows-2 100 (list w0 w1 w2 w3 w4 w5 w6 w7))) :ok)
              (wstatep (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-2 100 (list w0 w1 w2 w3 w4 w5 w6 w7)))))
  :g-bindings (gl::auto-bindings (:nat w0 32) (:nat w1 32) (:nat w2 32) (:nat w3 32) (:nat w4 32) (:nat w5 32) (:nat w6 32) (:nat w7 32)))

(defthm result-kind-of-isr2
  (implies (wstatep s) (equal (result-kind (aes-fixslice-encrypt-inv-shift-rows-2 100 s)) :ok))
  :hints (("Goal" :in-theory (e/d (expand-len-8 wstatep) (isr2-struct-gl aes-fixslice-encrypt-inv-shift-rows-2 nth))
           :use (:instance isr2-struct-gl (w0 (nth 0 s)) (w1 (nth 1 s)) (w2 (nth 2 s)) (w3 (nth 3 s)) (w4 (nth 4 s)) (w5 (nth 5 s)) (w6 (nth 6 s)) (w7 (nth 7 s))))))

(defthm wstatep-of-isr2
  (implies (wstatep s) (wstatep (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-2 100 s))))
  :hints (("Goal" :in-theory (e/d (expand-len-8 wstatep) (isr2-struct-gl aes-fixslice-encrypt-inv-shift-rows-2 nth))
           :use (:instance isr2-struct-gl (w0 (nth 0 s)) (w1 (nth 1 s)) (w2 (nth 2 s)) (w3 (nth 3 s)) (w4 (nth 4 s)) (w5 (nth 5 s)) (w6 (nth 6 s)) (w7 (nth 7 s))))))

(defthm inv-shift-rows-2-at-is
  (implies (and (natp off) (<= (+ off 8) (len rkeys)) (< (len rkeys) 4294967296)
                (wstatep (rd8 rkeys off)))
           (equal (aes-fixslice-encrypt-inv-shift-rows-2-at 100 rkeys off)
                  (ok (w8-spec 0 8 rkeys off
                        (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-2 100 (rd8 rkeys off)))))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-2-at len-when-wstatep true-listp-when-wstatep) (aes-fixslice-encrypt-inv-shift-rows-2 w8-spec rd8 nth)))))

;; ---- inv_shift_rows_3: wstate permutation, and its at-op = w8-spec ----
(gl::def-gl-thm isr3-struct-gl
  :hyp (and (unsigned-byte-p 32 w0) (unsigned-byte-p 32 w1) (unsigned-byte-p 32 w2) (unsigned-byte-p 32 w3) (unsigned-byte-p 32 w4) (unsigned-byte-p 32 w5) (unsigned-byte-p 32 w6) (unsigned-byte-p 32 w7))
  :concl (and (equal (result-kind (aes-fixslice-encrypt-inv-shift-rows-3 100 (list w0 w1 w2 w3 w4 w5 w6 w7))) :ok)
              (wstatep (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-3 100 (list w0 w1 w2 w3 w4 w5 w6 w7)))))
  :g-bindings (gl::auto-bindings (:nat w0 32) (:nat w1 32) (:nat w2 32) (:nat w3 32) (:nat w4 32) (:nat w5 32) (:nat w6 32) (:nat w7 32)))

(defthm result-kind-of-isr3
  (implies (wstatep s) (equal (result-kind (aes-fixslice-encrypt-inv-shift-rows-3 100 s)) :ok))
  :hints (("Goal" :in-theory (e/d (expand-len-8 wstatep) (isr3-struct-gl aes-fixslice-encrypt-inv-shift-rows-3 nth))
           :use (:instance isr3-struct-gl (w0 (nth 0 s)) (w1 (nth 1 s)) (w2 (nth 2 s)) (w3 (nth 3 s)) (w4 (nth 4 s)) (w5 (nth 5 s)) (w6 (nth 6 s)) (w7 (nth 7 s))))))

(defthm wstatep-of-isr3
  (implies (wstatep s) (wstatep (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-3 100 s))))
  :hints (("Goal" :in-theory (e/d (expand-len-8 wstatep) (isr3-struct-gl aes-fixslice-encrypt-inv-shift-rows-3 nth))
           :use (:instance isr3-struct-gl (w0 (nth 0 s)) (w1 (nth 1 s)) (w2 (nth 2 s)) (w3 (nth 3 s)) (w4 (nth 4 s)) (w5 (nth 5 s)) (w6 (nth 6 s)) (w7 (nth 7 s))))))

(defthm inv-shift-rows-3-at-is
  (implies (and (natp off) (<= (+ off 8) (len rkeys)) (< (len rkeys) 4294967296)
                (wstatep (rd8 rkeys off)))
           (equal (aes-fixslice-encrypt-inv-shift-rows-3-at 100 rkeys off)
                  (ok (w8-spec 0 8 rkeys off
                        (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-3 100 (rd8 rkeys off)))))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-3-at len-when-wstatep true-listp-when-wstatep) (aes-fixslice-encrypt-inv-shift-rows-3 w8-spec rd8 nth)))))
