(declare-var x1 Int)
(declare-var x2 Int)

(synth-fun f ((x Int) (y Int)) Int)

(constraint (> (+ (f x1 x2) (f x2 x1)) (f (+ x1 x2) (+ x1 x2))))
(constraint (> (f x1 x2) (+ x1 x2)))

(check-synth)
