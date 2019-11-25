(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)

(synth-fun f ((x Int) (y Int)) Int)

(constraint (= (f (* 5 x1) (* -3 x2)) (f (* 7 x1) (* 2 x2))))
(constraint (= (f (* 2 x3) (+ 2 (* 3 x4))) (f (- (* 4 x4) 2) (* 5 x3))))
(constraint (= (f (+ x1 x2) (- x3 x4)) (f (+ x3 x4) (+ x3 4))))
(constraint (distinct (f 0 0) (f 2 5)))

; assumptions:
;(assert (= (* 5 x1) (* 7 x1)))       ; x1 = 0; x2 = 0
;(assert (= (* -3 x2) (* 2 x2)))
;(assert (= (* 2 x3) (- (* 4 x4) 2))) ; x3 = 1; x4 = 1
;(assert (= (+ 2 (* 3 x4)) (* 5 x3)))

(check-synth)
