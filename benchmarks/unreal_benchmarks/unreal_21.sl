(declare-var x1 Int)
(declare-var x2 Int)

(synth-fun f ((x Int) (y Int)) Int)

(constraint (< (f x1 x2) x1))
(constraint (> (f x2 x1) 5))

; assumptions:
;(assert (= x1 0))
;(assert (= x2 0))

(check-synth)
