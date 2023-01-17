import Debug.Trace

-- Expr    ::= "\" String "->" Expr
-- Expr    ::= AppExpr
-- AppExpr ::= Expr VarExpr
-- AppExpr ::= VarExpr
-- VarExpr ::= Var String
-- VarExpr ::= Number Int
-- VarExpr ::= Boolean Bool
-- VarExpr ::= S | K | I | B | C | W
-- VarExpr ::= VarExpr ':' Expr
-- VarExpr ::= '(' Expr ')'

data Expr = Var String | Number Int | Boolean Bool | App Expr Expr | Abs String Expr | S | K | I | B | C | W | P
    deriving (Show)

-- old pretty print which generates lots of extra parenthesis
pp' :: Expr -> String
pp' (Var s) = show s
pp' (Number n) = show n
pp' (Boolean b) = show b
pp' (App e1 e2) = "(" <> pp' e1 <> " " <> pp' e2 <> ")"
pp' (Abs x e) = "\\" <> x <> "." <> (pp' e)
pp' (S) = "S"
pp' (K) = "K"
pp' (I) = "I"
pp' (B) = "B"
pp' (C) = "C"
pp' (W) = "W"
--pp' (P e1 e2) = pp' e1 <> ":" <> pp' e2
pp' (P) = "P"

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
ppvar (P) = "P"
--ppvar (P e1 e2) = pp e1 <> ":" <> pp e2
ppvar e = "(" <> pp e <> ")"


gen :: Expr -> String
gen (Var "plus") = "mkPLUS()"
gen (Var "times") = "mkTIMES()"
gen (Var "minus") = "mkMINUS()"
gen (Var "nil") = "mkNIL()"
gen (Var "eq") = "mkEQ()"
gen (Var "cond") = "mkCOND()"
gen (Var "head") = "mkHEAD()"
gen (Var "tail") = "mkTAIL()"
gen (Var "null") = "mkNULL()"
gen (Var s) = s
gen (Number n) = "mknum(" ++ (show n) ++ ")"
gen (App e1 e2) = "mkapply(" ++ gen(e1) ++ ", " ++ gen(e2) ++ ")"
gen S = "mkS()"
gen K = "mkK()"
gen I = "mkI()"
gen B = "mkB()"
gen C = "mkC()"
gen W = "mkW()"
--gen (P e1 e2) = "mkcons(" ++ gen(e1) ++ ", " ++ gen(e2) ++ ")"
gen P = "mkP()"
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
--translate (P e1 e2) = P
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
     putStrLn (gen (simplify (translate fac)) ++ ";") >>
     putStrLn (pp ex1) >>
     putStrLn (pp (translate ex1)) >>
     putStrLn (pp (simplify (translate ex1))) >>
     putStrLn (gen (simplify (translate ex1)) ++ ";") >>
     putStrLn (pp ex2) >>
     putStrLn (pp (translate ex2)) >>
     putStrLn (pp (simplify (translate ex2))) >>
     putStrLn (gen (simplify (translate ex2)) ++ ";") >>
     putStrLn (pp klenexpr) >>
     putStrLn (pp (translate klenexpr)) >>
     putStrLn (pp (simplify (translate klenexpr))) >>
     putStrLn (gen (simplify (translate klenexpr)) ++ ";")

  where
     -- fac x = if x = 0 then 1 else x * fac (x-1)
     -- fac = lambda x: cond =(x,0) 1 *(x, fac(-(x,1))
     -- fac = lambda x: cond e1 e2 e3  where e1 is =(x,0)  e2 is 1  e3 is *(x, fac(-(x,1)))
     e1 = App (App (Var "eq") (Var "x")) (Number 0)
     e2 = Number 1
     e3 = App (App (Var "times") (Var "x")) (App (Var "fac") (App (App (Var "minus") (Var "x")) (Number 1)))
     fac = Abs "x" (App (App (App (Var "cond") e1) e2) e3)
     -- \x.\y.cons(x,y)
     ex1 = Abs "x" (Abs "y" (App (App P (Var "x")) (Var "y")))
     ex2 = Abs "x" (Abs "y" (cons (Var "x") (cons (Var "y") (Var "nil"))))
     cons x y = App (App P x) y
     -- klen x = if null x then 0 else 1 + klen (tail x)
     ke1 = App (Var "null") (Var "x")
     ke2 = Number 0
     ke4 = App (Var "klen") (App (Var "tail") (Var "x"))
     ke3 = App (App (Var "plus") (Number 1)) ke4
     klen = Abs "x" (App (App (App (Var "cond") ke1) ke2) ke3)
     klenexpr = App klen (cons (Number 1) (cons (Number 2) (Var "nil")))

