(declare-var x1 Int)
(declare-var x2 Int)

(synth-fun f ((x Int)) Int)

(constraint (> (+ (f x1) (f x2)) (+ x1 x2 1)))
(constraint (> (+ (f x1) (f x2)) (* 10 x1)))
(constraint (> (+ (f x1) (f x2)) (* 10 x2)))

(check-synth)
