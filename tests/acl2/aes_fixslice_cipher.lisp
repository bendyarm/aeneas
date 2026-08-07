; Phase 5 -- CIPHER SIDE, part 1: the extracted aes128_encrypt collapses onto
; a clean value-chain model.
;
; The extracted body is bitslice ; ark@0 ; 9x[sub_bytes ; mix_columns_c ;
; ark@8r] ; shift_rows_2 ; sub_bytes ; ark@80 ; inv_bitslice -- 33 ops,
; single-threaded.  As with the key schedule: (1) length-only :ok facts let
; every ok-binder collapse from array bounds alone; (2) enc-model is the same
; chain as a pure val-composition; (3) enc-collapse equates them.  The round
; keys enter only through add_round_key's window reads, captured by arkw
; (word-wise xor against rd8), so the schedule windows plug in directly.
(in-package "ACL2")
(include-book "aes_fixslice_keymain")
(local (include-book "std/lists/nth" :dir :system))
(local (in-theory (disable len-when-wstatep true-listp-when-wstatep nth-when-zp)))

;; ===========================================================================
;; (C1) add_round_key: loop spec (word-wise xor against the rkeys window).
(defund arkw (s w)
  (list (u32-xor (nth 0 s) (nth 0 w)) (u32-xor (nth 1 s) (nth 1 w))
        (u32-xor (nth 2 s) (nth 2 w)) (u32-xor (nth 3 s) (nth 3 w))
        (u32-xor (nth 4 s) (nth 4 w)) (u32-xor (nth 5 s) (nth 5 w))
        (u32-xor (nth 6 s) (nth 6 w)) (u32-xor (nth 7 s) (nth 7 w))))

;; step/base for the extracted loop (write8-loop0 template).
(defthm ark-loop0-base
  (implies (and (natp i) (natp e) (<= e i) (not (zp n)))
           (equal (aes-fixslice-encrypt-add-round-key-loop0 n (rng i e) s rk off) (ok s)))
  :hints (("Goal" :expand ((aes-fixslice-encrypt-add-round-key-loop0 n (rng i e) s rk off))
           :in-theory (enable rnext-on-range))))
(defthm ark-loop0-step
  (implies (and (natp i) (natp e) (< i e) (not (zp n)) (natp off)
                (< (+ off i) (len rk)) (< (len rk) 4294967296) (< i (len s)))
           (equal (aes-fixslice-encrypt-add-round-key-loop0 n (rng i e) s rk off)
                  (aes-fixslice-encrypt-add-round-key-loop0 (1- n) (rng (+ i 1) e)
                    (update-nth i (u32-xor (nth i s) (nth (+ off i) rk)) s) rk off)))
  :hints (("Goal" :expand ((aes-fixslice-encrypt-add-round-key-loop0 n (rng i e) s rk off))
           :in-theory (e/d (rnext-on-range) (u32-xor)))))

;; generic accumulator spec for the loop, then the 8-step instance is arkw.
(defun arkw-spec (i e s rk off)
  (declare (xargs :measure (nfix (- (nfix e) (nfix i)))))
  (if (and (natp i) (natp e) (< i e))
      (arkw-spec (+ i 1) e (update-nth i (u32-xor (nth i s) (nth (+ off i) rk)) s) rk off)
    s))
(defun arkw-ind (n i e s rk off)
  (declare (xargs :measure (nfix (- (nfix e) (nfix i)))))
  (if (and (natp i) (natp e) (< i e) (not (zp n)) (< i (len s)))
      (arkw-ind (1- n) (+ i 1) e (update-nth i (u32-xor (nth i s) (nth (+ off i) rk)) s) rk off)
    (list n i e s rk off)))
(defthm ark-loop0-is-spec
  (implies (and (natp i) (natp e) (<= i e) (natp off) (<= (+ off e) (len rk))
                (< (len rk) 4294967296) (<= e (len s)) (< (- e i) (nfix n)))
           (equal (aes-fixslice-encrypt-add-round-key-loop0 n (rng i e) s rk off)
                  (ok (arkw-spec i e s rk off))))
  :hints (("Goal" :induct (arkw-ind n i e s rk off)
           :in-theory (e/d () (aes-fixslice-encrypt-add-round-key-loop0 u32-xor nth
                               (:executable-counterpart core-ops-range-range-usize-))))))
