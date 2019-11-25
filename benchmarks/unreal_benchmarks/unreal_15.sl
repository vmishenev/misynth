(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)

(synth-fun f ((x Int)) Int)

(constraint (or (= 0 (f x1)) (= 1 (f x2))))
(constraint (> 0 (+ (f x3) (f x4))))

; assumptions:
;(assert (= x1 x2))
;(assert (= x1 x3))
;(assert (= x1 x4))

(check-synth)
