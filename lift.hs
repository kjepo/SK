import Debug.Trace

-- Expr    ::= "\" String "->" Expr
-- Expr    ::= AppExpr
-- AppExpr ::= Expr VarExpr
-- AppExpr ::= VarExpr
-- VarExpr ::= Var String
-- VarExpr ::= Number Int
-- VarExpr ::= Boolean Bool
-- VarExpr ::= S | K | I | B | C | W
-- VarExpr ::= '(' Expr ')'

data Expr = Var String | Number Int | Boolean Bool | App Expr Expr | Abs String Expr | S | K | I | B | C | W
    deriving (Show)

pp :: Expr -> String
pp (Abs s e) = "\\" <> s <> " -> " <> pp e 
pp e = ppapp e

ppapp :: Expr -> String
ppapp (App f x) = pp f <> " " <> ppvar x
ppapp e = ppvar e

ppvar :: Expr -> String
ppvar (Var s) = s
ppvar (Number n) = show n
ppvar (Boolean b) = show b
ppvar (S) = "S"
ppvar (K) = "K"
ppvar (I) = "I"
ppvar (B) = "B"
ppvar (C) = "C"
ppvar (W) = "W"
ppvar e = "(" <> pp e <> ")"

gen :: Expr -> String
gen (Var "plus") = "mkPLUS()"
gen (Var "times") = "mkTIMES()"
gen (Var "minus") = "mkMINUS()"
gen (Var "eq") = "mkEQ()"
gen (Var "cond") = "mkCOND()"
gen (Var s) = s
gen (Number n) = "mknum(" ++ (show n) ++ ")"
gen (App e1 e2) = "mkapply(" ++ gen(e1) ++ ", " ++ gen(e2) ++ ")"
gen S = "mkS()"
gen K = "mkB()"
gen I = "mkI()"
gen B = "mkB()"
gen C = "mkC()"
gen W = "mkW()"
gen _ = "*error*"

-- list of all free variables in an expression
fv :: Expr -> [String]
fv (Var s) = [s]
fv (App e1 e2) = fv e1 ++ fv e2
fv (Abs x e) = [var | var <- fv e, var /= x]
fv _ = []

-- is x a free variable in an expression?
free :: String -> Expr -> Bool
free x e = elem x (fv e)

-- rules from https://en.wikipedia.org/wiki/Combinatory_logic
translate :: Expr -> Expr
translate (Var s) = Var s    -- (1)
translate (App e1 e2) = App (translate e1) (translate e2)    -- (2)
translate (Abs x e) | not (free x e) = App K (translate e)    -- (3)
translate (Abs x (Var x')) | x == x' = I    -- (4)
translate (Abs x (Abs y e)) | free x e = translate (Abs x (translate (Abs y e)))    -- (5)
translate (Abs x (App e1 e2)) | (free x e1 && free x e2) = App (App S (translate (Abs x e1))) (translate (Abs x e2)) -- (6)
translate (Abs x (App e1 e2)) | (free x e1 && not (free x e2)) = App (App C (translate (Abs x e1))) (translate e2) -- (7)
translate (Abs x (App e1 e2)) | (not (free x e1) && free x e2) = App (App B (translate e1)) (translate (Abs x e2)) -- (8)
translate e = e

-- question: should simplify be called repeatedly until fixedpoint or is it enough to be recursive?
simplify :: Expr -> Expr
simplify (App (App S (App K x)) I) = simplify x    -- S (K x) I == x
simplify (App (App S (App K x)) y) = App (App B (simplify x)) (simplify y)    -- S (K x) y == B x y
simplify (App (App S x) (App K y)) = App (App C (simplify x)) (simplify y)    -- S x (K y) == C x y
simplify (App (App B f) I) = simplify f    -- B f I = f
simplify (App C I) = C    -- C I = C  (kpt)
-- simplify (App (App (App C f) g) x) = App (App f x) g    -- C f g x = f x g  (kpt)
simplify (App e1 e2) = App (simplify e1) (simplify e2)    -- No match so simplify children
simplify e = e    -- Base case

main =
     print fac >>
     putStrLn (pp fac) >>
     putStrLn (pp (translate fac)) >>
     putStrLn (pp (simplify (translate fac))) >>
     putStr "Noderef facp = " >>
     putStrLn (gen (simplify (translate fac)) ++ ";")
  where
     -- fac x = if x = 0 then 1 else x * fac (x-1)
     -- fac = lambda x: cond =(x,0) 1 *(x, fac(-(x,1))
     -- fac = lambda x: cond e1 e2 e3  where e1 is =(x,0)  e2 is 1  e3 is *(x, fac(-(x,1)))
     e1 = App (App (Var "eq") (Var "x")) (Number 0)
     e2 = Number 1
     e3 = App (App (Var "times") (Var "x")) (App (Var "fac") (App (App (Var "minus") (Var "x")) (Number 1)))
     fac = (Abs "x") (App (App (App (Var "cond") e1) e2) e3)

