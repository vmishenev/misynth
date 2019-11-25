(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)

(synth-fun f ((x Int)) Int)

(constraint (> (f (+ (* 2 x1) (* 3 x2))) (- (* 5 (f x1)) (f x2))))
(constraint (< (f (+ (* 4 x3) (* 2 x4))) (+ (f x3) (* 3 (f x4)))))

; assumptions:
;(assert (= (+ (* 2 x1) (* 3 x2)) (+ (* 4 x3) (* 2 x4))))
;(assert (= x1 x2))
;(assert (= x3 x4))
;(assert (= x1 x3))

(check-synth)
