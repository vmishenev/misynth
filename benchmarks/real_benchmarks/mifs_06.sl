(declare-var x1 Int)
(declare-var x2 Int)

(synth-fun f ((x Int)) Int)

;(constraint (ite (> x1 x2) (> (f (+ x1 7)) x2) (> (f (- x2 13)) x1)))

(constraint (ite (> (+ x1 x2) 0) (> (f x1) (+ x1 10)) (> (f x2) 0)))

(constraint (> (f x1) x1 ))
(check-synth)
