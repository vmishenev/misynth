(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)

(synth-fun f ((x Int)) Int)

(constraint (> (f (+ x2 x4)) (+ (f x1) (f x3))))
(constraint (< (f (+ x1 x3)) (+ (f x2) (f x4))))

; assumptions:
;(assert (= x1 x2))
;(assert (= x3 x4))

(check-synth)
