(declare-var x1 Int)
(declare-var y1 Int)
(declare-fun R ( (Int) )  Bool)


(constraint ( => ( and (R x1) (R y1)) (= x1 y1) ))

