(declare-var x1 Int)
(declare-var y1 Int)
(declare-fun R_0 ( (Int) )  Bool)
(declare-fun R_1 ( (Int) )  Bool)

(constraint ( => (and (R_1 x1) (R_1 y1)) ( and (= 0 x1) (= 0 y1)) ))

