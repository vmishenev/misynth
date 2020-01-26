(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)
(declare-var x5 Int)
(declare-var x6 Int)

(synth-fun f ((x Int) (y Int) (z Int)) Int)

(constraint (> (f (+ x1 x2) (+ x3 x4) (* 2 (+ x5 x6))) (+ 1 (* 4 (f x1 x3 x5)) (* 2 (f x2 x4 x6)))))

(constraint (= (f x1 x2 x3) (f x1 x2 x3)))
(constraint (> (f x1 x2 x3) x3))

(check-synth)
