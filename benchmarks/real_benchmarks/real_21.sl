(declare-var x1 Int)
(declare-var x2 Int)

(synth-fun f ((x Int) (y Int)) Int)

(constraint (> (f x1 x2) x1))
(constraint (> (f x2 x1) x1))
(constraint (> (f x1 x2) (+ x1 x2)))
(constraint (> (f x2 x1) (- x1 x2)))
(constraint (> (f x1 x2) (+ x1 (* 2 x2))))
(constraint (> (f x2 x1) (- (* 2 x1) x2)))
(constraint (> (f x1 x2) (+ (* 3 x1) (* 2 x2))))
(constraint (> (f x2 x1) (- (* 2 x1) (* 4 x2))))

(check-synth)
