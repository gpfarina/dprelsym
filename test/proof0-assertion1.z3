(declare-fun log (Real) Real)
(define-fun max ((x1 Real) (x2 Real)) Real
   (ite (<= x1 x2) x2 x1))
(assert (forall ((a Real) (b Real))
        (and
                (=> (<= a b) (<= (log a) (log b)))
                (=> (and (>= a 0) (>= b 0) )
                        (>= (+ (log a) (log b)) (log a))
                (= (log 1.0) 0.0)
                (=> (< a 1) (< (log a) 0))
                (=> (> a 1) (> (log a) 0))
                )
        )
)
)

(assert (not (forall ( (EPS Real)  (X6 Real)  (I1 Bool)  (I2 Bool)  (X4 Bool)  (X5 Bool)  (X7 Bool)  (X8 Bool) ) (=> (and 
(not (= X8 I2)
)
(not (= X7 I1)
)
(not ( = X4 true)
)
(not ( = X5 true)
)
(= X6 (+ 0. 0.))
(= X4 X5)
(not (= I1 I2)
)
(= EPS (log 2.))
) (and (= X7 X8) (<= X6 EPS))))))
(check-sat)