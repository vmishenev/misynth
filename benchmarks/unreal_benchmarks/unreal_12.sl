(declare-var x1 Int)
(declare-var x2 Int)

(synth-fun f ((x Int)) Int)

(constraint (< (f (- x1 1)) (+ x1 1)))
(constraint (> (f (+ x1 1)) (+ x1 2)))

; should first rename x1 to x2 in the first constraint and get the following constraint:
;(assert (< (f (- x2 1)) (+ x2 1)))

; then, the assumption should be about (+ x1 1) and (- x2 1):
;(assert (= (+ x1 1) (- x2 1)))

(check-synth)
