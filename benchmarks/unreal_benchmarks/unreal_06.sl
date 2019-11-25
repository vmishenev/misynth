(declare-var x1 Int)
(declare-var x2 Int)

(synth-fun f ((x Int)) Int)

(constraint (= (f x1) (f x2)))
(constraint (distinct (f 1) (f 2)))

; assumptions:
;(assert (= x1 1))
;(assert (= x2 2))

(check-synth)
