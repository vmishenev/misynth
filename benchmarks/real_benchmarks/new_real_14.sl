(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)

(synth-fun f ((x Int)) Int)

(constraint (>  (+ (f x1) (f x2) (f x3) (f x4))
                (+ (* 4 x1) x2 x3 x4)))

(constraint (> (f x1) 4))

(check-synth)
