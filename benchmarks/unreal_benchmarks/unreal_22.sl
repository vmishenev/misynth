(declare-var x1 Int)
(declare-var x2 Int)

(synth-fun f ((x Int) (y Int)) Int)

(constraint (>= (f x1 x2) (+ x1 x2)))
(constraint (<= (f x2 x1) x1))

; should first rename (x2, x1) in the second constraint to (x1, x2) and get the following constraint:
;(assert (<= (f x1 x2) x2))

; assumption:
;(assert (= x1 1))

(check-synth)
