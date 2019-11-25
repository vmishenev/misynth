(declare-var x1 Int)
(declare-var x2 Int)

(synth-fun f ((x Int) (y Int)) Int)

(constraint (> (f (* 2 x1) (* 3 x2)) (f (* 3 x1) (* 2 x2))))

; assumptions:
;(assert (= (* 2 x1) (* 3 x1)))
;(assert (= (* 3 x2) (* 2 x2)))

(check-synth)
