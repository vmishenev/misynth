(declare-var x1 Int)

(synth-fun f ((x Int)) Int)

(constraint (< (f (- x1 1)) (+ (* 2 x1) 5)))
(constraint (> (f (+ x1 1)) (* 2 x1)))

(check-synth)
