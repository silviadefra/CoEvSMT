; Variable declarations
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const d Int)
(declare-const e Int)

; Constraints
(assert (> (* a b) 10))
(assert (< (* b c) 6))
(assert (> c 2))
(assert (> e (* d d)))
(assert (> d c))

; Solve
(check-sat)
(get-model)
