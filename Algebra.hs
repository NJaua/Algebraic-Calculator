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

groupAtoms :: Term -> Term
groupAtoms (Const p q) = Const p q
groupAtoms (Var x) = Var x
groupAtoms (Fun f t) = Fun f (groupAtoms t)
groupAtoms (Integ t1 t2) = Integ (groupAtoms t1) t2
groupAtoms (Exp t n) = Exp (groupAtoms t) n
groupAtoms (Sum t1 t2) = Sum (groupAtoms t1) (groupAtoms t2)
groupAtoms (Mult (Mult t1 t2) t3) = groupAtoms (Mult t1 (Mult t2 t3))
groupAtoms (Mult t1 t2) = groupAtoms' t1 (groupAtoms t2)
    where
        groupAtoms' t1 (Mult t2 t3)
            | compareTerm t1 t2 == LT = Mult t1 (Mult t2 t3)
            | compareTerm t1 t2 == EQ = Mult (increase t1 t2) t3
            | otherwise = Mult t2 (groupAtoms' t1 t3)
        groupAtoms' t1 t2
            | compareTerm t1 t2 == LT = Mult t1 t2
            | compareTerm t1 t2 == EQ = increase t1 t2
            | otherwise = Mult t2 t1
        increase (Exp (Const p1 q1) n1) (Exp (Const p2 q2) n2) = Exp (Const ((p1^n1)*(p2^n2)) ((q1^n1)*(q2^n2))) 1
        increase (Exp (Const p1 q1) n1) (Const p2 q2) = Exp (Const ((p1^n1)*p2) ((q1^n1)*q2)) 1
        increase (Const p1 q1) (Exp (Const p2 q2) n2) = Exp (Const (p1*(p2^n2)) (q1*(q2^n2))) 1
        increase (Const p1 q1) (Const p2 q2) = Exp (Const (p1*p2) (q1*q2)) 1
        increase (Exp t1 n1) (Exp t2 n2) = Exp t1 (n1+n2)
        increase (Exp t1 n1) t2 = Exp t1 (n1+1)
        increase t1 (Exp t2 n2) = Exp t1 (n2+1)
        increase t1 t2 = Exp t1 2

compareTerm :: Term -> Term -> Ordering
compareTerm (Const a b) (Const c d) = EQ
compareTerm (Const a b) (Exp (Const c d) n) = EQ
compareTerm (Const a b) _ = LT
compareTerm (Var x) (Const p q) = GT
compareTerm (Var x) (Var y) = compare x y
compareTerm (Var x) (Fun f t) = compare x f
compareTerm (Var x) (Exp t n) = compareTerm (Var x) t
compareTerm (Var x) _ = LT
compareTerm (Fun f t) (Const p q) = GT
compareTerm (Fun f t) (Var x) = compare f x
compareTerm (Fun f t) (Fun f2 t2)
    | f == f2   = compareTerm t t2
    | otherwise = compare f f2
compareTerm (Fun f t) (Exp t2 n) = compareTerm (Fun f t) t2
compareTerm (Fun f t) _ = LT
compareTerm (Sum t1 t2) (Const p q) = GT
compareTerm (Sum t1 t2) (Var x) = GT
compareTerm (Sum t1 t2) (Fun f t) = GT
compareTerm (Sum t1 t2) (Sum t3 t4)
    | t1 /= t3  = compareTerm t1 t3
    | otherwise = compareTerm t2 t4
compareTerm (Sum t1 t2) (Exp t n) = compareTerm (Sum t1 t2) t
compareTerm (Sum t1 t2) _ = LT
compareTerm (Mult t1 t2) (Mult t3 t4)
    | t1 /= t3  = compareTerm t1 t3
    | otherwise = compareTerm t2 t4
compareTerm (Mult t1 t2) (Exp t n) = compareTerm (Mult t1 t2) t
compareTerm (Mult t1 t2) (Integ t3 t4) = LT
compareTerm (Mult t1 t2) _ = GT
compareTerm (Integ t1 t2) (Exp t n) = compareTerm (Integ t1 t2) t
compareTerm (Integ t1 t2) (Integ t3 t4) = compareTerm t1 t3
compareTerm (Integ t1 t2) _ = GT
compareTerm (Exp t1 n) t2 = compareTerm t1 t2




test = groupAtoms t
    where
        t1 = 2
        t2 = x
        t3 = y
        t4 = Const 4 2
        t5 = Exp (sen (2*x)) 2
        t6 = Const 4 2
        t7 = Integ x x
        t8 = sen (2*x)
        t9 = Mult (Mult y z) x
        t10 = Exp x 2
        t11 = Sum x x
        t12 = x
        t = t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12