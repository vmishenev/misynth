(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)
(declare-var x5 Int)
(declare-var x6 Int)
(declare-var x7 Int)
(declare-var x8 Int)
(declare-var x9 Int)
(declare-var x10 Int)
(declare-var x11 Int)
(declare-var x12 Int)
(declare-var x13 Int)
(declare-var x14 Int)
(declare-var x15 Int)
(declare-var x16 Int)
(declare-var x17 Int)
(declare-var x18 Int)
(declare-var x19 Int)
(declare-var x20 Int)

(synth-fun f ((x Int) (y Int) (z Int) (w Int) (v Int)) Int)

(constraint (< (+ (* 3 (f x1 x2 x3 x4 x5))
                  (* 6 (f x6 x7 x8 x9 x10))
                  (* 8 (f x11 x12 x13 x14 x15))
                  (* 2 (f x16 x17 x18 x19 x20)))
            (+ (* 3 x1) (* 2 x2) (* 7 x3) (* 5 x4) (* 6 x5)
               (* 2 x6) (* 3 x7) (* 8 x8) (* 4 x9) (* 7 x10)
               (* 5 x11) (* 6 x12) (* 2 x13) (* 4 x14) (* 9 x15)
               (* 4 x16) (* 7 x17) (* 8 x18) (* 2 x19) (* 5 x20))))

(check-synth)