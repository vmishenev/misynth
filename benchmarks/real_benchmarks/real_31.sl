(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)

(synth-fun f ((x Int) (y Int) (z Int) (w Int)) Int)

(constraint (> (f x1 x2 x3 x4) (+ (- x1 x2) (- x3 x4))))
(constraint (= (f x1 x2 x3 x4) (f x4 x2 x3 x1)))

(check-synth)
