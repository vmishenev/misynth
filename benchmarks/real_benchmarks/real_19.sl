(declare-var x1 Int)
(declare-var x2 Int)

(synth-fun f ((x Int)) Int)

(constraint (ite (> x1 x2) (> (f (+ x1 7)) x2) (> (f (- x2 13)) x1)))

(constraint (ite (> (+ x1 x2) 43) (> (f x1) (+ x1 28)) (> (f x2) 92)))

(check-synth)
