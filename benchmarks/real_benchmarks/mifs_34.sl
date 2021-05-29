(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)

(synth-fun f ((x Int) (y Int) (z Int)) Int)

(constraint (ite (= x2 0) (>= (f x1 x2 x3) (+ x1 x2)) (< (f x1 x2 x3) x2)))
(constraint (= (f x1 x2 x3) (f x3 x2 x1)))

(check-synth)
