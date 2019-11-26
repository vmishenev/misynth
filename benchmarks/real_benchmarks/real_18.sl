(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)

(synth-fun f ((x Int)) Int)

(constraint (or (< (f (+ x1 x2 x3 x4)) (+ x1 x2 x3 x4))
                (> (f (+ x1 x2 x3 x4)) (+ x1 (* 2 x2) x3 x4))
                (< (f (+ x1 x2 x3 x4)) (+ x1 (* 2 x2) (* 3 x3) x4))
                (> (f (+ x1 x2 x3 x4)) (+ x1 (* 2 x2) (* 3 x3) (* 4 x4)))))

(constraint (or (> (f (+ x1 x2 x3 x4)) (+ x1 x2 x3 x4))
                (< (f (+ x1 x2 x3 x4)) (+ x1 (* 3 x2) x3 x4))
                (> (f (+ x1 x2 x3 x4)) (+ x1 (* 3 x2) (* 4 x3) x4))
                (< (f (+ x1 x2 x3 x4)) (+ x1 (* 3 x2) (* 4 x3) (* 5 x4)))))

(check-synth)
