(declare-var x1 Int)
(declare-var x2 Int)

(synth-fun f ((x Int)) Int)

(constraint (< (f (- x1 1)) 0))
(constraint (> (f x1) 0))

; should first rename x1 to x2 in the first constraint and get the following constraint:
;(assert (< (f (- x2 1)) 0))

; then, the assumption should be about x1 and (- x2 1):
;(assert (= x1 (- x2 1)))

(check-synth)
