(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)

(synth-fun f ((x Int)) Int)

(constraint (> (+ (* 2 (f x1))
                  (* 3 (f x2))
                  (* 5 (f x3))
                  (* 7 (f x4)))
            (+ (* 3 x1) (* 5 x2) (* 7 x3) (* 12 x4))))

(constraint (> (f x1) 8))

(check-synth)
