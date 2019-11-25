(declare-var x1 Int)
(declare-var x2 Int)

(synth-fun f ((x Int)) Int)

(constraint (> (f (+ x2 1)) x1))
(constraint (< (f (- x1 1)) x2))

; assumption:
;(assert (= (+ x2 1) (- x1 1)))

(check-synth)
