(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)
(declare-var x5 Int)
(declare-var x6 Int)

(synth-fun f ((x Int) (y Int)) Int)

(constraint (= (f x1 x2) (f x2 x1)))
(constraint (> (f x1 x2) (+ x1 x2)))
(constraint (distinct (f x1 x2) 0))

(check-synth)
