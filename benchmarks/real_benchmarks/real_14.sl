(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)

(synth-fun f ((x Int)) Int)

(constraint (>  (+ (f (+ x1 1)) (f (+ x2 2)) (f (+ x3 3)) (f (+ x4 4)))
                (* 10 (+ x1 x2 x3 x4))))

(check-synth)
