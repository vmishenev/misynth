(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)

(synth-fun f ((x Int) (y Int) (z Int)) Int)

(constraint (>= (f x1 x2 x3) (+ 1 (f x2 x3 x1) (f x3 x1 x2))))
(constraint (<= (f x1 x2 x3) (+ (f x3 x2 x1) (f x1 x3 x2) (f x2 x1 x3))))

; assumptions:
;(assert (= x1 x2))
;(assert (= x1 x3))

(check-synth)
