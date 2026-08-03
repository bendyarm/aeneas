(in-package "ACL2")
(include-book "tea")
;; Reference vectors (computed by an independent Python TEA implementation).
;; Fuel 33 > 32 rounds. Encrypt returns (cons y z).
(assert-event (equal (tea-encrypt 33 0 0 0 0 0 0) (ok (cons #x41ea3a0a #x94baa940))))
(assert-event (equal (tea-encrypt 33 #x12345678 #x9abcdef0 1 2 3 4)
                     (ok (cons #xf7995c6a #x182250b1))))
;; Round trip on the ACL2 side
(assert-event
 (equal (b* (((ok c) (tea-encrypt 33 #x12345678 #x9abcdef0 1 2 3 4)))
          (tea-decrypt 33 (car c) (cdr c) 1 2 3 4))
        (ok (cons #x12345678 #x9abcdef0))))
