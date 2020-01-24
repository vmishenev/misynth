(declare-var x1 Int)
(declare-var x2 Int)

(synth-fun f ((x Int)) Int)

(constraint (> (+ (f (* x1 2)) (f (* x2 2))) (+ x1 x2 10)))


(check-synth)
