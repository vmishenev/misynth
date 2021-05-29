(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)
(declare-var x5 Int)

(synth-fun f ((x Int) (y Int) (z Int) (w Int) (v Int)) Int)

(constraint (= (f x1 x2 x3 x4 x5) (f x5 x4 x3 x2 x1)))
(constraint (> (f x1 x2 x3 x4 x5) (* 10 x3)))
(constraint (distinct (f x1 x2 x3 x4 x5) 7))

(check-synth)
