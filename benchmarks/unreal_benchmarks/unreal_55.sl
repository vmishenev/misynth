(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)
(declare-var x5 Int)
(declare-var x6 Int)
(declare-var x7 Int)
(declare-var x8 Int)

(synth-fun f ((x Int) (y Int) (z Int) (w Int)) Int)

(constraint
      (= (f x1 x2 x3 x4)
            (ite (> (+ (f x1 x2 x3 x4) (f x5 x6 x7 x8))
                  (+ x1 x2 x3 x4 x5 x6 x7 x8))
                      0 1)))

(check-synth)
