(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)

(synth-fun f ((x Int)) Int)

(constraint (>= (+ (f x1) (f x2)) (+ x1 x2)))
(constraint (> 100 (f x3 )))

(check-synth)
