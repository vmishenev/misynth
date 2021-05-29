(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)

(synth-fun f ((x Int) (y Int) (z Int) (w Int)) Int)

(constraint (> (f x1 x2 x3 x4) (+ (* 2 x1) (* 3 x2) (* 4 x3) (* 5 x4))))
(constraint (> (f (* 2 x1) (* 3 x2) (* 4 x3) (* 5 x4)) (+ x1 x2 x3 x4)))

(check-synth)
