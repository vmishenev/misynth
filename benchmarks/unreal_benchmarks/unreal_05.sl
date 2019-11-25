(declare-var x1 Int)

(synth-fun f ((x Int)) Int)

(constraint (>= (f (+ x1 1)) (f x1)))
(constraint (> (f 1) (f 2)))

; assumption:
;(assert (= x1 1))

(check-synth)
