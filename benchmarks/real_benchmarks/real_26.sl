(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)

(synth-fun f ((x Int) (y Int) (z Int)) Int)

(constraint (> (+ (f x1 x2 x3) (f x3 x2 x1)) (f (+ x1 x2 x3) (+ x1 x2 x3) (+ x1 x2 x3))))
(constraint (> (f x1 x2 x3) x1))
(constraint (> (f x1 x2 x3) x2))
(constraint (> (f x1 x2 x3) x3))

(check-synth)
