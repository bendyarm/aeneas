; Phase 4 -- key-schedule CORE: one key_round step == the AES key-expansion
; recurrence, bit-blasted through the packing (both lanes = key, as the schedule
; bitslices key into both lanes; lane 0 shown). kr-spec-bytes is the recurrence
; (RotWord, SubWord via the inlined S-box table, Rcon, the running column XOR).
; One theorem per round constant (key_round differs only by rcon).
(in-package "ACL2")
(include-book "aes_fixslice_subbytes")

(defund xorw (x y) (list (logxor (nth 0 x)(nth 0 y)) (logxor (nth 1 x)(nth 1 y))
                         (logxor (nth 2 x)(nth 2 y)) (logxor (nth 3 x)(nth 3 y))))
(defund kr-spec-bytes (b rv)
  (b* ((w0 (list (nth 0 b)(nth 1 b)(nth 2 b)(nth 3 b)))
       (w1 (list (nth 4 b)(nth 5 b)(nth 6 b)(nth 7 b)))
       (w2 (list (nth 8 b)(nth 9 b)(nth 10 b)(nth 11 b)))
       (w3 (list (nth 12 b)(nth 13 b)(nth 14 b)(nth 15 b)))
       (rot (list (nth 1 w3)(nth 2 w3)(nth 3 w3)(nth 0 w3)))
       (sub (list (nth (nth 0 rot) *sbox*)(nth (nth 1 rot) *sbox*)
                  (nth (nth 2 rot) *sbox*)(nth (nth 3 rot) *sbox*)))
       (temp (list (logxor (nth 0 sub) rv)(nth 1 sub)(nth 2 sub)(nth 3 sub)))
       (n0 (xorw w0 temp)) (n1 (xorw w1 n0)) (n2 (xorw w2 n1)) (n3 (xorw w3 n2)))
    (append n0 n1 n2 n3)))

(gl::def-gl-thm key-round-step-rcon0
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15))
  :concl
  (let* ((b (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15))
         (rk0 (append (result-ok->val (aes-fixslice-encrypt-bitslice b b)) (make-list 80 :initial-element 0)))
         (rk1 (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100 rk0 0 0)))))
    (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (take 8 (nthcdr 8 rk1)))))
           (kr-spec-bytes b 1)))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8)))

(gl::def-gl-thm key-round-step-rcon1
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15))
  :concl
  (let* ((b (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15))
         (rk0 (append (result-ok->val (aes-fixslice-encrypt-bitslice b b)) (make-list 80 :initial-element 0)))
         (rk1 (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100 rk0 0 1)))))
    (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (take 8 (nthcdr 8 rk1)))))
           (kr-spec-bytes b 2)))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8)))

(gl::def-gl-thm key-round-step-rcon2
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15))
  :concl
  (let* ((b (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15))
         (rk0 (append (result-ok->val (aes-fixslice-encrypt-bitslice b b)) (make-list 80 :initial-element 0)))
         (rk1 (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100 rk0 0 2)))))
    (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (take 8 (nthcdr 8 rk1)))))
           (kr-spec-bytes b 4)))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8)))

(gl::def-gl-thm key-round-step-rcon3
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15))
  :concl
  (let* ((b (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15))
         (rk0 (append (result-ok->val (aes-fixslice-encrypt-bitslice b b)) (make-list 80 :initial-element 0)))
         (rk1 (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100 rk0 0 3)))))
    (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (take 8 (nthcdr 8 rk1)))))
           (kr-spec-bytes b 8)))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8)))

(gl::def-gl-thm key-round-step-rcon4
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15))
  :concl
  (let* ((b (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15))
         (rk0 (append (result-ok->val (aes-fixslice-encrypt-bitslice b b)) (make-list 80 :initial-element 0)))
         (rk1 (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100 rk0 0 4)))))
    (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (take 8 (nthcdr 8 rk1)))))
           (kr-spec-bytes b 16)))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8)))

(gl::def-gl-thm key-round-step-rcon5
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15))
  :concl
  (let* ((b (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15))
         (rk0 (append (result-ok->val (aes-fixslice-encrypt-bitslice b b)) (make-list 80 :initial-element 0)))
         (rk1 (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100 rk0 0 5)))))
    (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (take 8 (nthcdr 8 rk1)))))
           (kr-spec-bytes b 32)))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8)))

(gl::def-gl-thm key-round-step-rcon6
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15))
  :concl
  (let* ((b (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15))
         (rk0 (append (result-ok->val (aes-fixslice-encrypt-bitslice b b)) (make-list 80 :initial-element 0)))
         (rk1 (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100 rk0 0 6)))))
    (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (take 8 (nthcdr 8 rk1)))))
           (kr-spec-bytes b 64)))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8)))

(gl::def-gl-thm key-round-step-rcon7
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15))
  :concl
  (let* ((b (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15))
         (rk0 (append (result-ok->val (aes-fixslice-encrypt-bitslice b b)) (make-list 80 :initial-element 0)))
         (rk1 (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100 rk0 0 7)))))
    (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (take 8 (nthcdr 8 rk1)))))
           (kr-spec-bytes b 128)))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8)))

(gl::def-gl-thm key-round-step-rcon8
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15))
  :concl
  (let* ((b (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15))
         (rk0 (append (result-ok->val (aes-fixslice-encrypt-bitslice b b)) (make-list 80 :initial-element 0)))
         (rk1 (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100 rk0 0 8)))))
    (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (take 8 (nthcdr 8 rk1)))))
           (kr-spec-bytes b 27)))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8)))

(gl::def-gl-thm key-round-step-rcon9
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15))
  :concl
  (let* ((b (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15))
         (rk0 (append (result-ok->val (aes-fixslice-encrypt-bitslice b b)) (make-list 80 :initial-element 0)))
         (rk1 (cdr (result-ok->val (aes-fixslice-encrypt-key-round 100 rk0 0 9)))))
    (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (take 8 (nthcdr 8 rk1)))))
           (kr-spec-bytes b 54)))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8)))

;; ---------------------------------------------------------------------------
;; Bridge validation: iterating kr-spec-bytes from the key reproduces Kestrel's
;; keyexpansion round keys (so the step above = the spec's key-expansion step).
;; Concrete check on the FIPS-197 C.1 key; the all-inputs equality of
;; kr-spec-bytes to Kestrel's subword/rotword/rcon recurrence is a rewriting
;; bridge (subword uses (sbox); kr-spec-bytes uses *sbox* = (sbox), sbox-const-
;; correct).  This closes the "what does the step compute" question against spec.
(local
 (progn
   (defun kc-xpow (c) (if (zp c) 1 (aes::xtime (kc-xpow (1- c)))))
   (defun kc-iter (key r)  ; r-th round key by iterating kr-spec-bytes
     (declare (xargs :measure (nfix r)))
     (if (zp r) key (kr-spec-bytes (kc-iter key (1- r)) (kc-xpow (1- r)))))
   (defun kc-kk (w r)
     (append (nth (* 4 r) w) (nth (+ 1 (* 4 r)) w) (nth (+ 2 (* 4 r)) w) (nth (+ 3 (* 4 r)) w)))
   (defconst *kc-key* '(#x2b #x7e #x15 #x16 #x28 #xae #xd2 #xa6 #xab #xf7 #x15 #x88 #x09 #xcf #x4f #x3c))
   (defconst *kc-w*   (aes::keyexpansion *kc-key* 4))
   (defun kc-all (r)
     (declare (xargs :measure (nfix (- 11 r))))
     (if (or (not (natp r)) (> r 10)) t
       (and (equal (kc-iter *kc-key* r) (kc-kk *kc-w* r)) (kc-all (1+ r)))))
   ;; iterated recurrence == Kestrel keyexpansion, all 11 round keys:
   (assert-event (kc-all 0))))

;; ---------------------------------------------------------------------------
;; ROADMAP -- remaining chaining to  key_schedule core == bitslice(keyexpansion):
;; The step cruxes above give, for each rcon c and any 16-byte round key b:
;;   inv_bitslice( key_round(<bitslice(b,b) in a fresh array>, 0, c) @slot ) = kr-spec-bytes(b, xpow c),
;; and kr-spec-bytes iterated = Kestrel keyexpansion (validated above). What
;; remains is to CHAIN the 10 unrolled key_rounds through the 88-word rkeys
;; array: generalise the step to read8(rkeys,off)/write8(...,off+8) for arbitrary
;; off (key_round's write at off+8 depends only on rkeys[off..off+8]) with the
;; both-lanes-equal invariant, then rewrite the unrolled schedule down to
;; kr-spec-bytes iterated. read-over-write (nth/update-nth) lemmas carry the
;; array threading; the step cruxes carry each round.  The fold layer
;; (aes_fixslice_keyschedule) then adjusts to the final round keys.
