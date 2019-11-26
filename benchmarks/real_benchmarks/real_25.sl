(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)

(synth-fun f ((x Int) (y Int)) Int)

(constraint (> (f (+ x1 x2) (+ x3 x4)) (+ (f x1 x3) (f x2 x4))))
(constraint (< (f x1 x3) x1))
(constraint (< (f x1 x3) x3))
(constraint (< (f x1 x3) 0))

(check-synth)
