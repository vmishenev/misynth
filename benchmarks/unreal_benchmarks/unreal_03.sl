(declare-var x1 Int)
(declare-var x2 Int)

(synth-fun f ((x Int)) Int)

(constraint (distinct (f x1) x2))
(constraint (= (f x1) x2))

(check-synth)
