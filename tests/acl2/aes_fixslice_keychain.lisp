; Phase 4 -- key-schedule CORE chaining: the 10 unrolled key_round steps
; compute Kestrel's key expansion (bitsliced), for ALL inputs.
;
; Strategy (structured rewriting, no GL past the per-round cruxes in keycore):
;  * Each of the three schedule loop shapes (write8, memshift32, xor_columns)
;    is proven equal to an explicit window-update spec (w8/ms/xc-spec) with a
;    read-through (nth-of-*) lemma -- this gives LOCALITY and FRAME for free.
;  * key_round is then a pure window transform krw8 on rkeys[off..off+8),
;    writing rkeys[off+8..off+16); off-independent.
;  * The keycore cruxes (off=0) give inv_bitslice(krw8(bitslice(b,b),c)) =
;    kr-spec-bytes(b, xpow c); chaining the 10 disjoint windows then yields
;    inv_bitslice(window r) = kk(r) for every round key.
(in-package "ACL2")
(include-book "aes_fixslice_keycore")
(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "std/lists/update-nth" :dir :system))
(local (include-book "std/lists/nth" :dir :system))

;; This proof chain builds on the -gl extraction + centaur/gl (whose `fail`
;; FUNCTION rules out including range_for-proofs, which pulls in the `fail`
;; MACRO from rust-primitives).  rnext-on-range -- what the synthesized range
;; iterator's next does on a concrete range -- is re-derived here directly.
(defmacro rng (i e) `(core-ops-range-range-usize- ,i ,e))
(defmacro rnext (r)
  `(core-iter-range-impl-core-iter-traits-iterator-iterator-for-core-ops-range-range-usize-next-usize-
    ,r))
(defthm rnext-on-range
  (equal (rnext (rng i e))
         (if (< i e)
             (ok (cons (core-option-option-usize--some i) (rng (+ i 1) e)))
           (ok (cons (core-option-option-usize--none) (rng i e)))))
  :hints (("Goal" :in-theory
           (enable core-iter-range-impl-core-iter-traits-iterator-iterator-for-core-ops-range-range-usize-next-usize-))))

;; Fixed shifts (<32) and the rotate never fail -- lets the b* ok-binders in the
;; loop bodies resolve while u32-shl / ror stay opaque to arithmetic-5.
(defthm result-kind-u32-shl-small
  (implies (and (natp n) (< n 32))
           (equal (result-kind (u32-shl x n)) :ok))
  :hints (("Goal" :in-theory (enable u32-shl))))
(defthm result-kind-ror
  (equal (result-kind (aes-fixslice-encrypt-ror x y)) :ok)
  :hints (("Goal" :in-theory (enable aes-fixslice-encrypt-ror u32-rotate-right))))

;; ============================ write8 ============================
(defun w8-spec (i e rkeys off s)
  (declare (xargs :measure (nfix (- (nfix e) (nfix i)))))
  (if (and (natp i) (natp e) (< i e))
      (w8-spec (+ i 1) e (update-nth (+ off i) (nth i s) rkeys) off s)
    rkeys))
(defthm write8-loop0-step-rec
  (implies (and (natp i) (natp e) (< i e) (not (zp n))
                (natp off) (< (+ off i) (len rkeys)) (< (len rkeys) 4294967296) (< i (len s)))
           (equal (aes-fixslice-encrypt-write8-loop0 n (rng i e) rkeys off s)
                  (aes-fixslice-encrypt-write8-loop0 (1- n) (rng (+ i 1) e)
                       (update-nth (+ off i) (nth i s) rkeys) off s)))
  :hints (("Goal" :expand ((aes-fixslice-encrypt-write8-loop0 n (rng i e) rkeys off s))
                  :in-theory (enable rnext-on-range))))
(defthm write8-loop0-step-base
  (implies (and (natp i) (natp e) (<= e i) (not (zp n)))
           (equal (aes-fixslice-encrypt-write8-loop0 n (rng i e) rkeys off s) (ok rkeys)))
  :hints (("Goal" :expand ((aes-fixslice-encrypt-write8-loop0 n (rng i e) rkeys off s))
                  :in-theory (enable rnext-on-range))))
(defun w8-ind (n i e rkeys off s)
  (declare (xargs :measure (nfix (- (nfix e) (nfix i)))))
  (if (and (natp i) (natp e) (< i e) (not (zp n)))
      (w8-ind (1- n) (+ i 1) e (update-nth (+ off i) (nth i s) rkeys) off s)
    (list n i e rkeys off s)))
(defthm write8-loop0-is-w8spec
  (implies (and (natp i) (natp e) (<= i e) (natp off) (<= (+ off e) (len rkeys))
                (< (len rkeys) 4294967296) (<= e (len s)) (< (- e i) (nfix n)))
           (equal (aes-fixslice-encrypt-write8-loop0 n (rng i e) rkeys off s)
                  (ok (w8-spec i e rkeys off s))))
  :hints (("Goal" :induct (w8-ind n i e rkeys off s)
                  :do-not '(eliminate-destructors generalize)
                  :in-theory (e/d (w8-spec)
                                  (aes-fixslice-encrypt-write8-loop0 rnext-on-range
                                   (:executable-counterpart core-ops-range-range-usize-))))))
(defthm len-of-w8-spec
  (implies (and (natp i) (natp e) (natp off) (<= (+ off e) (len rkeys)))
           (equal (len (w8-spec i e rkeys off s)) (len rkeys))))
(defthm nth-of-w8-spec
  (implies (and (natp i) (natp e) (natp off) (natp k))
           (equal (nth k (w8-spec i e rkeys off s))
                  (if (and (< i e) (<= (+ off i) k) (< k (+ off e))) (nth (- k off) s) (nth k rkeys)))))
(defthm write8-is-w8spec
  (implies (and (natp off) (<= (+ off 8) (len rkeys)) (< (len rkeys) 4294967296) (<= 8 (len s)))
           (equal (aes-fixslice-encrypt-write8 100 rkeys off s)
                  (ok (w8-spec 0 8 rkeys off s))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-write8)
                                  (aes-fixslice-encrypt-write8-loop0 w8-spec))
                  :use (:instance write8-loop0-is-w8spec (i 0) (e 8) (n 100)))))

;; ============================ memshift32 ============================
(defun ms-spec (i e buffer src dst)
  (declare (xargs :measure (nfix (- (nfix e) (nfix i)))))
  (if (and (natp i) (natp e) (< i e))
      (ms-spec (+ i 1) e (update-nth (+ dst i) (nth (+ src i) buffer) buffer) src dst)
    buffer))
(defthm ms-loop0-step-rec
  (implies (and (natp i) (natp e) (< i e) (not (zp n)) (natp src) (natp dst)
                (< (+ src i) (len buffer)) (< (+ dst i) (len buffer)) (< (len buffer) 4294967296))
           (equal (aes-fixslice-encrypt-memshift32-loop0 n (rng i e) buffer src dst)
                  (aes-fixslice-encrypt-memshift32-loop0 (1- n) (rng (+ i 1) e)
                       (update-nth (+ dst i) (nth (+ src i) buffer) buffer) src dst)))
  :hints (("Goal" :expand ((aes-fixslice-encrypt-memshift32-loop0 n (rng i e) buffer src dst))
                  :in-theory (enable rnext-on-range))))
(defthm ms-loop0-step-base
  (implies (and (natp i) (natp e) (<= e i) (not (zp n)))
           (equal (aes-fixslice-encrypt-memshift32-loop0 n (rng i e) buffer src dst) (ok buffer)))
  :hints (("Goal" :expand ((aes-fixslice-encrypt-memshift32-loop0 n (rng i e) buffer src dst))
                  :in-theory (enable rnext-on-range))))
(defun ms-ind (n i e buffer src dst)
  (declare (xargs :measure (nfix (- (nfix e) (nfix i)))))
  (if (and (natp i) (natp e) (< i e) (not (zp n)))
      (ms-ind (1- n) (+ i 1) e (update-nth (+ dst i) (nth (+ src i) buffer) buffer) src dst)
    (list n i e buffer src dst)))
(defthm ms-loop0-is-msspec
  (implies (and (natp i) (natp e) (<= i e) (natp src) (natp dst)
                (<= (+ src e) (len buffer)) (<= (+ dst e) (len buffer))
                (< (len buffer) 4294967296) (< (- e i) (nfix n)))
           (equal (aes-fixslice-encrypt-memshift32-loop0 n (rng i e) buffer src dst)
                  (ok (ms-spec i e buffer src dst))))
  :hints (("Goal" :induct (ms-ind n i e buffer src dst)
                  :do-not '(eliminate-destructors generalize)
                  :in-theory (e/d (ms-spec)
                                  (aes-fixslice-encrypt-memshift32-loop0 rnext-on-range
                                   (:executable-counterpart core-ops-range-range-usize-))))))
(defthm len-of-ms-spec
  (implies (and (natp i) (natp e) (natp dst) (<= (+ dst e) (len buffer)))
           (equal (len (ms-spec i e buffer src dst)) (len buffer))))
(defthm nth-of-ms-spec
  (implies (and (natp i) (natp e) (natp src) (natp dst) (natp k) (<= (+ src e) dst))
           (equal (nth k (ms-spec i e buffer src dst))
                  (if (and (< i e) (<= (+ dst i) k) (< k (+ dst e)))
                      (nth (+ src (- k dst)) buffer) (nth k buffer)))))
(defthm memshift32-is-msspec
  (implies (and (natp src) (<= (+ src 16) (len buffer)) (< (len buffer) 4294967296))
           (equal (aes-fixslice-encrypt-memshift32 100 buffer src)
                  (ok (ms-spec 0 8 buffer src (+ src 8)))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-memshift32)
                                  (aes-fixslice-encrypt-memshift32-loop0 ms-spec))
                  :use (:instance ms-loop0-is-msspec (i 0) (e 8) (n 100) (dst (+ src 8))))))

;; ============================ xor_columns ============================
(defun xc-word (left cur dror)
  (b* (((ok v1092) (aes-fixslice-encrypt-ror cur dror))
       (v1093 (u32-and 50529027 v1092))
       (rk (u32-xor left v1093))
       ((ok v1095) (u32-shl rk 2))
       (v1096 (u32-and 4244438268 v1095))
       (v1097 (u32-xor rk v1096))
       ((ok v1098) (u32-shl rk 4))
       (v1099 (u32-and 4042322160 v1098))
       (v1100 (u32-xor v1097 v1099))
       ((ok v1101) (u32-shl rk 6))
       (v1102 (u32-and 3233857728 v1101))
       (v1103 (u32-xor v1100 v1102)))
    v1103))
(defthm xc-loop0-step-rec
  (implies (and (natp i) (natp e) (< i e) (not (zp n)) (natp off) (natp dx)
                (<= dx off) (< (+ off i) (len rkeys)) (< (len rkeys) 4294967296))
           (equal (aes-fixslice-encrypt-xor-columns-loop0 n (rng i e) rkeys off dx dror)
                  (aes-fixslice-encrypt-xor-columns-loop0 (1- n) (rng (+ i 1) e)
                       (update-nth (+ off i)
                                   (xc-word (nth (+ off i (- dx)) rkeys) (nth (+ off i) rkeys) dror)
                                   rkeys) off dx dror)))
  :hints (("Goal" :do-not-induct t :do-not '(eliminate-destructors generalize)
                  :expand ((aes-fixslice-encrypt-xor-columns-loop0 n (rng i e) rkeys off dx dror))
                  :in-theory (e/d (rnext-on-range xc-word result-kind-u32-shl-small result-kind-ror)
                                  (u32-and u32-xor u32-shl u32-or aes-fixslice-encrypt-ror)))))
(defthm xc-loop0-step-base
  (implies (and (natp i) (natp e) (<= e i) (not (zp n)))
           (equal (aes-fixslice-encrypt-xor-columns-loop0 n (rng i e) rkeys off dx dror) (ok rkeys)))
  :hints (("Goal" :expand ((aes-fixslice-encrypt-xor-columns-loop0 n (rng i e) rkeys off dx dror))
                  :in-theory (enable rnext-on-range))))
(defun xc-spec (i e rkeys off dx dror)
  (declare (xargs :measure (nfix (- (nfix e) (nfix i)))))
  (if (and (natp i) (natp e) (< i e))
      (xc-spec (+ i 1) e
               (update-nth (+ off i)
                           (xc-word (nth (+ off i (- dx)) rkeys) (nth (+ off i) rkeys) dror) rkeys)
               off dx dror)
    rkeys))
(defun xc-ind (n i e rkeys off dx dror)
  (declare (xargs :measure (nfix (- (nfix e) (nfix i)))))
  (if (and (natp i) (natp e) (< i e) (not (zp n)))
      (xc-ind (1- n) (+ i 1) e
              (update-nth (+ off i)
                          (xc-word (nth (+ off i (- dx)) rkeys) (nth (+ off i) rkeys) dror) rkeys)
              off dx dror)
    (list n i e rkeys off dx dror)))
(defthm xc-loop0-is-xcspec
  (implies (and (natp i) (natp e) (<= i e) (natp off) (natp dx) (<= dx off)
                (<= (+ off e) (len rkeys)) (< (len rkeys) 4294967296) (< (- e i) (nfix n)))
           (equal (aes-fixslice-encrypt-xor-columns-loop0 n (rng i e) rkeys off dx dror)
                  (ok (xc-spec i e rkeys off dx dror))))
  :hints (("Goal" :induct (xc-ind n i e rkeys off dx dror)
                  :do-not '(eliminate-destructors generalize)
                  :in-theory (e/d (xc-spec)
                                  (aes-fixslice-encrypt-xor-columns-loop0 rnext-on-range xc-word
                                   (:executable-counterpart core-ops-range-range-usize-))))))
(defthm len-of-xc-spec
  (implies (and (natp i) (natp e) (natp off) (<= (+ off e) (len rkeys)))
           (equal (len (xc-spec i e rkeys off dx dror)) (len rkeys)))
  :hints (("Goal" :in-theory (disable xc-word))))
(defthm nth-of-xc-spec
  (implies (and (natp i) (natp e) (natp off) (natp dx) (natp k) (<= e dx) (< 0 off))
           (equal (nth k (xc-spec i e rkeys off dx dror))
                  (if (and (< i e) (<= (+ off i) k) (< k (+ off e)))
                      (xc-word (nth (+ k (- dx)) rkeys) (nth k rkeys) dror) (nth k rkeys))))
  :hints (("Goal" :induct (xc-spec i e rkeys off dx dror)
                  :do-not '(eliminate-destructors generalize)
                  :in-theory (disable xc-word))))
(defthm xor-columns-is-xcspec
  (implies (and (natp off) (natp dx) (<= dx off) (<= (+ off 8) (len rkeys))
                (< (len rkeys) 4294967296))
           (equal (aes-fixslice-encrypt-xor-columns 100 rkeys off dx dror)
                  (ok (xc-spec 0 8 rkeys off dx dror))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-xor-columns)
                                  (aes-fixslice-encrypt-xor-columns-loop0 xc-spec))
                  :use (:instance xc-loop0-is-xcspec (i 0) (e 8) (n 100)))))

;; ============================ read8 ============================
(defun rd8 (rkeys off)
  (list (nth off rkeys) (nth (+ off 1) rkeys) (nth (+ off 2) rkeys) (nth (+ off 3) rkeys)
        (nth (+ off 4) rkeys) (nth (+ off 5) rkeys) (nth (+ off 6) rkeys) (nth (+ off 7) rkeys)))
(defthm read8-is-rd8
  (implies (and (natp off) (<= (+ off 8) (len rkeys)) (< (len rkeys) 4294967296))
           (equal (aes-fixslice-encrypt-read8 rkeys off) (ok (rd8 rkeys off))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (aes-fixslice-encrypt-read8) (nth)))))
