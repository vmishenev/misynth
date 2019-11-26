(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)

(synth-fun f ((x Int)) Int)

(constraint (>= (+ (f (+ x1 x3)) (f (+ x2 x4)))
                (+ x1 (* 2 x2) x3 (* 2 x4))))

(check-synth)
