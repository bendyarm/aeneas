; FIPS-197 Appendix C.1 known-answer test for the extracted fixsliced AES-128
; encrypt (aes_fixslice_encrypt.lisp, from the SHIPPED RustCrypto crate). The
; fixsliced expanded key *fips-rk* was produced by RUNNING the reference crate
; key schedule on the FIPS-197 key (00010203...0f); the extracted encrypt
; reproduces the standard's ciphertext (69c4e0d8...c55a) bit-for-bit.
(in-package "ACL2")
(include-book "aes_fixslice_encrypt")

(defconst *fips-rk*
  (list #xff00ff00 #xffff0000 #xcccccccc #xf0f0f0f0 #x00000000 #x00000000 #x00000000 #x00000000 #x33ffccff #xcc330000 #xf03cf0c3 #xf3033f30 #xffff00ff #x000000ff #x0000ff00 #xff00ffff #x0f003cff #xc33ccccc #x0c3fc03f #x3c0fc3f0 #xccccff33 #x33333300 #x33ccff33 #xccff3333 #x0c3303ff #x03f33cf0 #xfc3fc0f3 #xfccffc30 #xf03ccc0f #x0fc30fcc #xf00f00c3 #xf0ccc30f #x333c3000 #xf3c0fcfc #xf3cfffcf #xf3cc30f0 #xf33f0ffc #x0cc0c00f #x3ffccc0c #xf3c303fc #xf00c0f33 #xc0c000ff #x0cc333c3 #xf3c33ccf #x0cc0f333 #x0cc03030 #x30ff3ccf #xf3f3ffcc #xc00cc0c3 #x33303300 #xf0f3c33f #x3cf330c3 #xf0fc330f #xc3cf03c3 #xc0fffcf0 #xc30ccc3c #x3ffc0cf3 #xf03cf033 #xf30303f3 #xfc03ffc0 #x0c33c303 #xfc0f0ff3 #x3f003c03 #x30cff00c #xf0f03cfc #x3f0c0c3c #x330ffccf #x0cf0ccc0 #xfff0fc00 #xc0033f03 #x0f33fccc #xfc33c0fc #x3f3003ff #xcf033f3f #x3ccf33c3 #x3f030fc0 #xccfcccff #xfcccfc33 #x0c3cfff0 #xcc0ffccc #x00cc0c00 #xc0c30fc0 #xcf333cc0 #x330fc0c0 #x0fc30f33 #xfc0f3fc3 #x3cf3ff03 #xf0300c3c)
)

(defconst *fips-pt*
  (list #x00 #x11 #x22 #x33 #x44 #x55 #x66 #x77 #x88 #x99 #xaa #xbb #xcc #xdd #xee #xff))

(defconst *fips-ct*
  (list #x69 #xc4 #xe0 #xd8 #x6a #x7b #x04 #x30 #xd8 #xcd #xb7 #x80 #x70 #xb4 #xc5 #x5a))

;; The extracted fixsliced AES-128 encrypt reproduces the FIPS-197 C.1 vector.
;; (fuel 20 covers each add_round_key / shift_rows for-loop, 8 iterations.)
(assert-event
 (equal (aes-fixslice-encrypt-encrypt-block 20 *fips-rk* *fips-pt*)
        (ok *fips-ct*)))
