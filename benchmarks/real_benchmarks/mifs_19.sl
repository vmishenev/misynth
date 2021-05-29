(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)
(declare-var x5 Int)

(synth-fun f ((x Int)) Int)

(constraint (> (+ (f x1) (f x2) (f x3) (f x4) (f x5)) (+ (f x1) x2 x3 x4 x5 1)))
(constraint (> (+ (f x1) (f x2) (f x3) (f x4) (f x5)) (+ x1 (f x2) x3 x4 x5 2)))
(constraint (> (+ (f x1) (f x2) (f x3) (f x4) (f x5)) (+ x1 x2 (f x3) x4 x5 3)))
(constraint (> (+ (f x1) (f x2) (f x3) (f x4) (f x5)) (+ x1 x2 x3 (f x4) x5 4)))
(constraint (> (+ (f x1) (f x2) (f x3) (f x4) (f x5)) (+ x1 x2 x3 x4 (f x5) 5)))

(check-synth)
