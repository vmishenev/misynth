(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)
(declare-var x5 Int)
(declare-var x6 Int)

(synth-fun f ((x Int) (y Int) (z Int)) Int)


(constraint (= (f x1 x2 x3) (f x1 x2 x3)))
(constraint (> (f (* 2 x1) (* 3 x2) (* 4 x3)) (+ x1 x2 x3)))

(check-synth)
