--
-- Experiments in abstraction techniques: lambda expressions -> combinators
--

data Expr
    = Var String
    | Number Int
    | Boolean Bool
    | App Expr Expr
    | Abs String Expr
    | S
    | K
    | I
    | B
    | C
    | W
    | T Expr Expr

instance Show Expr where
	 show = showExpr

showExpr :: Expr -> String
showExpr (Var s) = s
showExpr (Number n) = show n
showExpr (Boolean b) = show b
showExpr (App e1 e2) = "(" ++ (showExpr e1) ++ " " ++ (showExpr e2) ++ ")"
showExpr (Abs x e) = "\\" ++ x ++ "." ++ (showExpr e)
showExpr (S) = "S"
showExpr (K) = "K"
showExpr (I) = "I"
showExpr (B) = "B"
showExpr (C) = "C"
showExpr (W) = "W"
showExpr (T e1 e2) = "(" ++ (showExpr e1) ++ " " ++ (showExpr e2) ++ ")"

reduce :: Expr -> Expr
reduce (Var s) = Var s
reduce (Number n) = Number n
reduce (Boolean b) = Boolean b
reduce (T I x) = x
reduce (T (T K x) y) = x
reduce (T (T (T S x) y) z) = reduce (T (T x z) (T y z))

-- list of all free variables in an expression
fv :: Expr -> [String]
fv (Var s) = [s]
fv (App e1 e2) = fv e1 ++ fv e2
fv (Abs x e) = [var | var <- fv e, var /= x]
fv (T e1 e2) = fv e1 ++ fv e2
fv _ = []

-- is x a free variable in an expression?
free :: String -> Expr -> Bool
free x e = elem x (fv e)

-- rules from https://en.wikipedia.org/wiki/Combinatory_logic
translate :: Expr -> Expr
-- rule 1
translate (Var s) = Var s
-- rule 2
translate (App e1 e2) = App (translate e1) (translate e2)
-- rule 3
translate (Abs x e) | not (free x e) = App K (translate e)
-- rule 4
translate (Abs x (Var x')) | x == x' = I
-- rule 5
translate (Abs x (Abs y e)) | free x e = translate (Abs x (translate (Abs y e)))
-- rule 6
translate (Abs x (App e1 e2)) | (free x e1 && free x e2) = App (App S (translate (Abs x e1))) (translate (Abs x e2))
-- rule 7
translate (Abs x (App e1 e2)) | (free x e1 && not (free x e2)) = App (App C (translate (Abs x e1))) (translate e2)
-- rule 8
translate (Abs x (App e1 e2)) | (not (free x e1) && free x e2) = App (App B (translate e1)) (translate (Abs x e2))
-- default
translate e = e

simplify :: Expr -> Expr
simplify (App (App S (App K x)) I) = simplify x
simplify (App (App S (App K x)) y) = App (App B (simplify x)) (simplify y)
simplify (App e1 e2) = App (simplify e1) (simplify e2)
simplify e = e

eval :: Expr -> Expr
eval (Number x) = Number x
eval (App I x) = eval x
eval (App (App K x) y) = eval x
eval (App (App (App S x) y) z) = eval (App (App x y) (App x z))

main =
     print (App (Number 3) (Var "x")) >>
     print (Abs "x" (Var "x")) >>
     print expr1 >>
     print (T (T (T S K) K) (Number 17)) >>
     print (T (T (T S K) K) (Number 42)) >>
     print (reduce (T (T (T S K) K) (Number 42))) >>
     print (fv expr1) >>
     print (free "+" expr1)  >>
     print expr2 >>
     print (translate expr2) >>
     print (simplify (translate expr2))

  where
     -- double x = x + x
     -- double = lambda x : (+ x) x
     expr1 = (Abs "x" (App (App (Var "+") (Var "x")) (Var "x")))
     -- lambda x: lambda y: y x 
     expr2 = (Abs "x" (Abs "y" (App (Var "y") (Var "x"))))
     expr3 = (Abs "x" (Var "y"))
     expr4 = (Abs "x" (Var "x"))
     expr5 = (Abs "x" (Abs "y" (Abs "z" (App (App (Var "x") (Var "z")) (App (Var "y") (Var "z"))))))
     expr6 = (Abs "x" (App (Var "x") (Var "x")))

