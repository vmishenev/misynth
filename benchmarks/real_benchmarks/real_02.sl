(declare-var x1 Int)

(synth-fun f ((x Int)) Int)

(constraint (< (f (- x1 1)) x1))
(constraint (> (f (+ x1 1)) x1))

(check-synth)
