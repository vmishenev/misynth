(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)
(declare-var x5 Int)
(declare-var x6 Int)
(declare-var x7 Int)
(declare-var x8 Int)

(synth-fun f ((x Int)) Int)

(constraint (= (f (+ x1 x2 x3 x4 x5 x6 x7 x8)) (+ (f x1) (f x2) (f x3) (f x4) (f x5) (f x6) (f x7) (f x8))))
(constraint (distinct (f (+ x1 x2)) (+ (f x1) (f x2))))

; assumptions:

;(assert (= (+ x1 x2 x3 x4 x5 x6 x7 x8) x1))
;(assert (= (+ x1 x2 x3 x4 x5 x6 x7 x8) x2))
;(assert (= (+ x1 x2 x3 x4 x5 x6 x7 x8) x3))
;(assert (= (+ x1 x2 x3 x4 x5 x6 x7 x8) x4))
;(assert (= (+ x1 x2 x3 x4 x5 x6 x7 x8) x5))
;(assert (= (+ x1 x2 x3 x4 x5 x6 x7 x8) x6))
;(assert (= (+ x1 x2 x3 x4 x5 x6 x7 x8) x7))
;(assert (= (+ x1 x2 x3 x4 x5 x6 x7 x8) x8))


(check-synth)
