(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (not (=> (and (<= x 3) (or (<= y 7) (<= z 9))) (or (<= (+ x y) 10) (<= (+ x z) 12)))))
(check-sat)
(exit)
