module Term where

data Term = Const Int Int
          | Var String
          | Fun String Term
          | Integ Term Term
          | Sum Term Term
          | Mult Term Term
          | Exp Term Int

t :: Term
t = Var "t"
u :: Term
u = Var "u"
v :: Term
v = Var "v"
w :: Term
w = Var "w"
x :: Term
x = Var "x"
y :: Term
y = Var "y"
z :: Term
z = Var "z"

sen::(Term)->Term
sen (t1) = Fun "sen" t1
cosen::(Term)->Term
cosen (t1) = Fun "cos" t1

showTerm:: Term -> String
showTerm (Const n 1)
    | n>=0 = show n
    | n<=0 = "(" ++ (show n) ++ ")"
showTerm (Const p q) = "\\frac{" ++ (show p) ++ "}{" ++ (show q) ++ "}"
showTerm (Var x) = x
showTerm (Fun "sen" t) = "sin(" ++ (show t) ++ ")"
showTerm (Fun "cos" t) = "cos(" ++ (show t) ++ ")"
showTerm (Integ t x) = "\\int " ++ (show t) ++ "d" ++ (show x)
showTerm (Sum t1 t2) = (show t1) ++ "+" ++ (show t2)
showTerm (Mult (Const a b) (Const c d))= (show (Const a b))++"*"++(show (Const c d))
showTerm (Mult (Sum t1 t2) (Sum t3 t4)) = "("++(show (Sum t1 t2)) ++ ")" ++ "("++(show (Sum t3 t4)) ++ ")"
showTerm (Mult (Sum t1 t2) t3) = "("++(show (Sum t1 t2)) ++ ")" ++ (show t3)
showTerm (Mult t3 (Sum t1 t2)) = (show t3) ++ "("++(show (Sum t1 t2)) ++ ")"
showTerm (Mult t1 t2) = (show t1) ++ (show t2)
showTerm (Exp (Var x) n) = x ++ "^{" ++ (show n) ++ "}"
showTerm (Exp (Const a 1) n) = (show (Const a 1)) ++ "^{" ++ (show n) ++ "}"
showTerm (Exp (Exp a m) n) = (show (Exp a m)) ++ "^{" ++ (show n) ++ "}"
showTerm (Exp (Fun "sen" t0) n) = "sin" ++ "^{" ++ (show n) ++ "}(" ++ (show t0) ++")"
showTerm (Exp (Fun "cos" t0) n) = "cos" ++ "^{" ++ (show n) ++ "}(" ++ (show t0) ++")"
showTerm (Exp t0 n) = "(" ++ (show t0) ++ ")^{" ++ (show n) ++ "}"
instance Show Term where show t = showTerm t

instance Num Term where
    fromInteger x = (Const (fromIntegral x) 1)
    x + y = (Sum x y)
    x * y = (Mult x y)
    abs x = error ""
    signum x = error ""
    negate (Const a b) = (Const (-a) b)
    negate x = (Mult (Const (-1) 1) x)

instance Eq Term where
    (Const a b) == (Const c d) = a==c && b==d 
    (Var x) == (Var y) = x==y
    (Fun f t) == (Fun g u) = f==g && t==u
    (Integ t1 x1) == (Integ t2 x2) = t1==t2 && x1==x2
    (Sum t1 t2) == (Sum t3 t4) = t1==t3 && t2==t4
    (Mult t1 t2) == (Mult t3 t4) = t1==t3 && t2==t4
    (Exp t1 i1) == (Exp t2 i2) = t1==t2 && i1==i2
    _==_ = False