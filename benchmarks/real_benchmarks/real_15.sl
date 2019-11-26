(declare-var x1 Int)
(declare-var x2 Int)

(synth-fun f ((x Int)) Int)

(constraint (or (> (+ (f x1) (f x2)) x1)
                (< (+ (f x1) (f x2)) x2)))
(constraint (or (> (f (+ x1 x2)) (+ (f x1) (f x2)))
                (< (f (- x1 x2)) (- (f x1) (f x2)))))

(check-synth)
