(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)
(declare-var x5 Int)
(declare-var x6 Int)

(synth-fun f ((x Int) (y Int) (z Int)) Int)

(constraint (> (f (+ x1 x2) (+ x3 x4) (+ x5 x6)) (+ (f x1 x3 x5) (f x2 x4 x6))))
(constraint (< (f (- x1 x2) (- x3 x4) (- x5 x6)) (- (f x1 x3 x5) (f x2 x4 x6))))
(constraint (or (< (f x1 x3 x5) x1) (< (f x1 x3 x5) x3) (< (f x1 x3 x5) x5)))

(check-synth)
