(declare-var x1 Int)

(synth-fun f ((x Int)) Int)

(constraint (< (f x1) 0))
(constraint (> (f (* 2 x1)) 0))

; assumption:
;(assert (= x1 (* 2 x1)))

(check-synth)
