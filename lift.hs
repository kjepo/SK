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
gen (Var "equal") = "mkEQUAL()"
gen (Var "notequal") = "mkNOTEQUAL()"
gen (Var "lessthan") = "mkLESSTHAN()"
gen (Var "greaterthan") = "mkGREATERTHAN()"
gen (Var "not") = "mkNOT()"
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

compile :: Expr -> String -> IO ()
compile e s =
	--        putStrLn ("// " ++ (pp (translate e))) >>
        putStrLn ("// " ++ (pp (simplify (translate e)))) >>
        putStrLn ("DEF(" ++ s ++ ", " ++ (gen (simplify (translate e))) ++ ");")

main =
     compile list10 "list10"
  where
     sum = (Abs "n" ((App (App (App (Var "cond")  (App (App (Var "equal") (Var "n") ) (Number 0)) ) (Number 0)) (App (App (Var "plus") (Var "n") ) (App (Var "sum")  (App (App (Var "minus") (Var "n") ) (Number 1)) )) ))) 
     sign = (Abs "x" ((App (App (App (Var "cond")  (App (App (Var "lessthan") (Var "x") ) (Number 0)) ) (App (App (Var "minus") (Number 0)) (Number 1)) ) (App (App (App (Var "cond")  (App (App (Var "greaterthan") (Var "x") ) (Number 0)) ) (Number 1)) (Number 0))))) 
     fac = (Abs "x" ((App (App (App (Var "cond")  (App (App (Var "equal") (Var "x") ) (Number 0)) ) (Number 1)) (App (App (Var "times") (Var "x") ) (App (Var "fac")  (App (App (Var "minus") (Var "x") ) (Number 1)) )) ))) 
     len = (Abs "xs" ((App (App (App (Var "cond")  (App (Var "null")  (Var "xs") )) (Number 0)) (App (App (Var "plus") (Number 1)) (App (Var "len")  (App (Var "tail")  (Var "xs") ))) ))) 
     ack = (Abs "x" ((Abs "y" ((App (App (App (Var "cond")  (App (App (Var "equal") (Var "y") ) (Number 0)) ) (App (App (Var "ack")  (App (App (Var "minus") (Var "x") ) (Number 1)) ) (Number 1))) (App (App (App (Var "cond")  (App (App (Var "equal") (Var "x") ) (Number 0)) ) (App (App (Var "plus") (Var "y") ) (Number 1)) ) (App (App (Var "ack")  (App (App (Var "minus") (Var "x") ) (Number 1)) ) (App (App (Var "ack")  (Var "x") ) (App (App (Var "minus") (Var "y") ) (Number 1)) )))))) )) 
     --      list2 = (App (App P (App (App P (Number 1)) (Number 2)) ) (Var "nil") ) 
     list2 = (App (App P (Number 1)) (App (App P (Number 2)) (Var "nil") ) )
     list3 = (App (App P (Number 1)) (App (App P (Number 2)) (App (App P (Number 3)) (Var "nil") ) ) ) 
--     list10 = (App (App P (Number 1)) (App (App P (Number 2)) (App (App P (Number 3)) (App (App P (Number 4)) (App (App P (Number 5)) (App (App P (Number 6)) (App (App P (Number 7)) (App (App P (Number 8)) (App (App P (Number 9)) (App (App P (Number 10)) (Var "nil") ) ) ) ) ) ) ) ) ) )   
     tail12 = (App (Var "tail")  (App (App P (Number 1)) (App (App P (Number 2)) (Var "nil") ) ) )
     list10 = (App (App P (Number 1)) (App (App P (Number 2)) (App (App P (Number 3)) (App (App P (Number 4)) (App (App P (Number 5)) (App (App P (Number 6)) (App (App P (Number 7)) (App (App P (Number 8)) (App (App P (Number 9)) (App (App P (Number 10)) (Var "nil") ) ) ) ) ) ) ) ) ) ) 