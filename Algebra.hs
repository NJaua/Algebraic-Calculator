module Algebra where

import Term

simplify:: Term -> Term
simplify (Exp 0 0) = error "0^0 undefined"
simplify (Const 0 0) = error "0/0 undefined"
simplify (Exp t 0) = Const 1 1
simplify (Exp t 1) = t
simplify (Exp (Const p q) n) = simplify (Const (p^n) (q^n))
simplify (Const p q) = Const (p`div`(gcd p q)) (q`div`(gcd p q)) 
simplify (Sum (Const a b) (Const c d)) = simplify (Const (a*d + c*b) (b*d))
simplify (Mult (Const a b) (Const c d)) = simplify (Const (a*c) (b*d))
simplify (Sum (Const 0 n) t) = t
simplify (Sum t (Const 0 n)) = t
simplify (Mult (Const 1 1) t) = t
simplify (Mult t (Const 1 1)) = t
simplify (Var x) = Var x
simplify (Sum t1 (Mult (Const a b) t2))
    | t1 == t2 = Mult (Const (a+b) b) (simplify t1)
simplify (Sum t1 (Mult t2 (Const a b)))
    | t1 == t2 = Mult (Const (a+b) b) (simplify t1)
simplify (Sum (Mult (Const a b) t2) t1)
    | t1 == t2 = Mult (Const (a+b) b) (simplify t1)
simplify (Sum (Mult t2 (Const a b)) t1)
    | t1 == t2 = Mult (Const (a+b) b) (simplify t1)
simplify (Sum (Mult (Const a b) t1) (Mult (Const c d) t2))
    | t1 == t2 = Mult (simplify (Const (a*d + c*b) (b*d))) (simplify t1)
simplify (Sum (Mult t1 (Const a b)) (Mult (Const c d) t2))
    | t1 == t2 = Mult (simplify (Const (a*d + c*b) (b*d))) (simplify t1)
simplify (Sum (Mult (Const a b) t1) (Mult t2 (Const c d)))
    | t1 == t2 = Mult (simplify (Const (a*d + c*b) (b*d))) (simplify t1)
simplify (Sum (Mult t1 (Const a b)) (Mult t2 (Const c d)))
    | t1 == t2 = Mult (simplify (Const (a*d + c*b) (b*d))) (simplify t1)
simplify (Sum t1 t2)
    | t1 == t2 = Mult (Const 2 1) (simplify t1)
    | otherwise = Sum (simplify t1) (simplify t2)
simplify (Mult t1 t2) = Mult (simplify t1) (simplify t2)
simplify (Integ t1 t2) = Integ (simplify t1) (simplify t2)
simplify (Fun f t) = Fun f (simplify t)
simplify (Exp t n) = Exp (simplify t) n

distrib:: Term -> Term
distrib (Var x) = Var x
distrib (Const n m) = Const n m
distrib (Mult t1 (Sum t2 t3)) = distrib (Sum (distrib (Mult t1 t2)) (distrib (Mult t1 t3)))
distrib (Mult (Sum t2 t3) t1) = distrib (Sum (distrib (Mult t2 t1)) (distrib (Mult t3 t1)))
distrib (Mult (Mult t1 t2) (Mult t3 t4)) = distrib (Mult (distrib (Mult t1 t2)) (distrib (Mult t3 t4)))
distrib (Mult t1 t2) = (Mult (distrib t1) (distrib t2))
distrib (Sum t1 t2) = (Sum (distrib t1) (distrib t2))
distrib (Fun f t) = (Fun f (distrib t))
distrib (Exp t n) = (Exp (distrib t) n)
distrib (Integ t1 t2) =Integ (distrib t1) (distrib t2)

pow:: Term->Term
pow (Var x) = Var x
pow (Const n m) = Const n m
pow (Exp 0 0) = error ""
pow (Exp a 0) = Const 1 1
pow (Exp a 1) = pow a
pow (Exp (Const p q) n) = Const (p^n) (q^n)
pow (Exp (Exp t n) m) = Exp (pow t) (n*m)
pow (Exp (Mult t1 t2) n) = Mult (pow (Exp t1 n)) (pow (Exp t2 n))
pow (Exp (Sum t1 t2) n) = newtonBin t1 t2 n 0
    where
        newtonBin t1 t2 n i 
            | n==i = t2
            | otherwise = (Sum (Mult (Const (binCof n i) 1) (Mult (pow (Exp t1 (n-i))) (pow (Exp t2 i)))) (newtonBin t1 t2 n (i+1)))
            where
                binCof n i
                    | n==i || i==0 = 1
                    | otherwise = (binCof (n-1) i)+(binCof (n-1) (i-1))
pow (Mult t1 t2) = (Mult (pow t1) (pow t2))
pow (Sum t1 t2) = (Sum (pow t1) (pow t2))
pow (Fun f t) = (Fun f (pow t))
pow (Exp t n) = (Exp (pow t) n)
pow (Integ t1 t2) = Integ (pow t1) (pow t2)