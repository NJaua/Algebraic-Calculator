module Antidiff where

import Term

simbInt :: Term -> Term
simbInt (Const p q) = Const p q
simbInt (Var x) = Var x
simbInt (Fun f t) = Fun f (simbInt t)
simbInt (Exp t n) = Exp (simbInt t) n
simbInt (Sum t1 t2) = (simbInt t1) + (simbInt t2)
simbInt (Mult t1 t2) = (simbInt t1) * (simbInt t2)
simbInt (Integ (Const p q) x) = (Const p q) * x
simbInt (Integ (Mult (Const p q) t) x) = (Const p q) * (Integ t x)
simbInt (Integ (Sum t1 t2) x) = (Integ t1 x) + (Integ t2 x)
simbInt (Integ (Exp t k) x)
    | t == x = (Const 1 (k+1)) * (Exp x (k+1))
simbInt (Integ t x)
    | not (occurs t x) = t * x
simbInt (Integ (Fun "sen" t) x)
    | t == x = (-1) * (cosen x)
simbInt (Integ (Fun "cos" t) x)
    | t == x = sen x
simbInt (Integ (Fun "sen" (Mult (Const p 1) t)) x)
    | t == x = (Const (-1) p) * (cosen ((Const p 1) * x))
simbInt (Integ (Fun "cos" (Mult (Const p 1) t)) x)
    | t == x = (Const 1 p) * (sen ((Const p 1) * x))
simbInt (Integ (Mult (Fun "cos" x1) (Exp (Fun "sen" x2) n)) x3)
    | x1 == x2 && x2 == x3 = (Const 1 (n+1)) * (Exp (sen x) (n+1))
simbInt (Integ (Mult (Exp (Fun "cos" x1) n) (Fun "sen" x2)) x3)
    | x1 == x2 && x2 == x3 = (Const (-1) (n+1)) * (Exp (cosen x) (n+1))
simbInt (Integ (Mult (Fun "cos" (Mult (Const k1 1) x1)) (Exp (Fun "sen" (Mult (Const k2 1) x2)) n)) x3)
    | x1 == x2 && x2 == x3 && k1 == k2 = (Const 1 (k1*(n+1))) * (Exp (sen (Mult (Const k1 1) x)) (n+1))
simbInt (Integ (Mult (Exp (Fun "cos" (Mult (Const k1 1) x1)) n) (Fun "sen" (Mult (Const k2 1) x2))) x3)
    | x1 == x2 && x2 == x3 && k1 == k2 = (Const (-1) (k1*(n+1))) * (Exp (cosen (Mult (Const k1 1) x)) (n+1))
simbInt (Integ (Exp (Fun "sen" t) n) x)
    | t == x && even n = Integ (Exp ((Const 1 2) * (1 + (-1)*(cosen (2*x)))) (n`div`2)) x
    | t == x && odd  n = Integ ((Exp (1 + (-1)*(Exp (cosen x) 2)) ((n-1)`div`2)) * (sen x)) x
simbInt (Integ (Exp (Fun "cos" t) n) x)
    | t == x && even n = Integ (Exp ((Const 1 2) * (1 + (cosen (2*x)))) (n`div`2)) x
    | t == x && odd  n = Integ ((Exp (1 + (-1)*(Exp (sen x) 2)) ((n-1)`div`2)) * (cosen x)) x
simbInt (Integ (Exp (Fun "sen" (Mult k t)) n) x)
    | t == x && even n = Integ (Exp ((Const 1 2) * (1 + (-1)*(cosen (2*k*x)))) (n`div`2)) x
    | t == x && odd  n = Integ ((Exp (1 + (-1)*(Exp (cosen (k*x)) 2)) ((n-1)`div`2)) * (sen (k*x))) x
simbInt (Integ (Exp (Fun "cos" (Mult k t)) n) x)
    | t == x && even n = Integ (Exp ((Const 1 2) * (1 + (cosen (2*k*x)))) (n`div`2)) x
    | t == x && odd  n = Integ ((Exp (1 + (-1)*(Exp (sen (k*x)) 2)) ((n-1)`div`2)) * (cosen (k*x))) x

occurs :: Term -> Term -> Bool
occurs (Const p q) (Var x) = False
occurs (Var y) (Var x) = y == x
occurs (Fun f t) (Var x) = occurs t (Var x)
occurs (Integ t d) (Var x) = (occurs t (Var x)) || (occurs d (Var x))
occurs (Sum t1 t2) (Var x) = (occurs t1 (Var x)) || (occurs t2 (Var x))
occurs (Mult t1 t2) (Var x) = (occurs t1 (Var x)) || (occurs t2 (Var x))
occurs (Exp t n) (Var x) = occurs t (Var x)