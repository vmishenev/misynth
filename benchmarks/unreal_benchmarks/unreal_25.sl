(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)

(synth-fun f ((x Int) (y Int)) Int)
(constraint (= (f x1 (+ x3 x4)) (+ (f x1 x3) x4)))
(constraint (distinct (f (+ x1 x2) x3) (+ x1 (f x2 x3))))

; assumptions:
;(assert (= (+ x3 x4) x3))
;(assert (= (+ x1 x2) x2))
;(assert (= (+ x1 x2) x1))

(check-synth)
