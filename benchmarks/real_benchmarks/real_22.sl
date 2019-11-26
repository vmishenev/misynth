(declare-var x1 Int)
(declare-var x2 Int)

(synth-fun f ((x Int) (y Int)) Int)

(constraint (>= (f x1 x2) x1))
(constraint (>= (f x2 x1) x1))
(constraint (or (<= (f x1 x2) (+ x1 x2)) (<= (f x1 x2) (- x1 x2))
                (<= (f x2 x1) (- x1 x2)) (<= (f x2 x1) (- x1 (- x2)))))

; isn't the second constraint equivalent to this?
;(constraint (or (<= (f x1 x2) (+ x1 x2)) (<= (f x1 x2) (- x1 x2))
;   (<= (f x1 x2) (- x2 x1)) (<= (f x1 x2) (- x1 (- x2)))))

(check-synth)
