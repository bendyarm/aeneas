; Known-answer regression for the LE byte plumbing (de-vendoring roadmap
; item 6): u32::from_le_bytes over slice.try_into().unwrap() (through a
; shared subslice read + core's own Result), and to_le_bytes written back
; through copy_from_slice on a mutable subslice borrow.
(in-package "ACL2")
(include-book "lebytes_probe")
(local (include-book "arithmetic-5/top" :dir :system))

;; ld: bytes 2..6 of the array, little-endian.
;; 3 + 4*256 + 5*65536 + 6*16777216 = 101057539... computed by ACL2 itself.
(defthm ld-known-answer
  (equal (lebytes-probe-ld (list 1 2 3 4 5 6 7 8))
         (ok (+ 3 (* 4 256) (* 5 65536) (* 6 16777216)))))

;; st: 0x0d0c0b0a's LE bytes spliced into [2,6) of an all-zero 8-array.
(defthm st-known-answer
  (equal (lebytes-probe-st 218893066)  ; #x0d0c0b0a
         (ok (list 0 0 10 11 12 13 0 0))))

;; round trip at the u32 level.
(defthm le-round-trip
  (implies (u32p w)
           (equal (u32-from-le-bytes (u32-to-le-bytes w)) w))
  :hints (("Goal" :in-theory (enable u32-from-le-bytes u32-to-le-bytes u32p))))

;; nested single-element + range mutable borrow (the upstream inv_bitslice
;; write shape: output[k][a..b].copy_from_slice(...)).
(defthm st2-known-answer
  (equal (lebytes-probe-st2 218893066)  ; #x0d0c0b0a
         (ok (list (list 0 0 0 0 0 0 0 0)
                   (list 0 0 10 11 12 13 0 0)))))
