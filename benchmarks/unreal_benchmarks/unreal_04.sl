(declare-var x1 Int)

(synth-fun f ((x Int)) Int)

(constraint (>= (f x1) x1))
(constraint (< (f x1) 8))

; assumption (can only be guessed):
;(assert (= x1 8))

(check-synth)
