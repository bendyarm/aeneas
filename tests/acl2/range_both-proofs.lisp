; Known-answer checks for range_both.rs (Range<usize> and Range<i32> used
; together).  One Range model serves both instantiations; certifying this
; book shows loops over each extract, admit, and execute.
(in-package "ACL2")
(include-book "range_both")

(assert-event (equal (range-both-sum-usize 100 (list 1 2 3 4)) (ok 10)))
(assert-event (equal (range-both-count-i32 100) (ok 10)))
