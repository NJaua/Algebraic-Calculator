import Term
import Algebra
import Antidiff

simplifyIO :: Term -> IO Term
simplifyIO x
    | x == y = return x
    | otherwise = do {appendFile "index.html" $ "$$="++(show y)++"$$\n"; return y}
    where
        y = simplify x

powIO :: Term -> IO Term
powIO x
    | x == y = return x
    | otherwise = do {appendFile "index.html" $ "$$="++(show y)++"$$\n"; return y}
    where
        y = pow x

distribIO :: Term -> IO Term
distribIO x
    | x == y = return x
    | otherwise = do {appendFile "index.html" $ "$$="++(show y)++"$$\n"; return y}
    where
        y = distrib x

groupAtomsIO :: Term -> IO Term
groupAtomsIO x
    | x == y = return x
    | otherwise = do {appendFile "index.html" $ "$$="++(show y)++"$$\n"; return y}
    where
        y = groupAtoms x

simbIntIO :: Term -> IO Term
simbIntIO x
    | x == y = return x
    | otherwise = do {appendFile "index.html" $ "$$="++(show y)++"$$\n"; return y}
    where
        y = simbInt x

solve :: Term -> IO Term
solve x = do {writeFile "index.html" $ "<html>\n"
                                    ++ "<head>\n"
                                    ++ "<link rel=\"stylesheet\" href=\"http://stilgar.ldc.usb.ve/Aledania/static/css/bootstrap.min.css\" >\n"
                                    ++ "<script src=\"http://stilgar.ldc.usb.ve/Aledania/static/js/bootstrap.min.js\"></script>\n"
                                    ++ "<script type=\"text/javascript\" src=\"http://stilgar.ldc.usb.ve/Aledania/static/js/mathjax-MathJax-v2.3-248-g60e0a8c/MathJax.js?config=TeX-AMS-MML_HTMLorMML\">\n"
                                    ++ "</script>\n"
                                    ++ "</head>\n"
                                    ++ "<body>\n";
            appendFile "index.html" $ "$$" ++ (show $ groupAtoms x) ++ "$$\n";
            solveAux (Const 1 1) (groupAtoms x)}
    where
        solveAux :: Term -> Term -> IO Term
        solveAux x y 
            | x == y = do {appendFile "index.html" "</body>\n</html>\n"; return x}
            | otherwise = return y >>= simbIntIO >>= powIO >>= distribIO >>= groupAtomsIO >>= simplifyIO >>= (solveAux y)