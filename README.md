# SK

A small implementation of David Turner's graph reduction algorithm from
"A new implementation technique for applicative languages", Software Practice
& Experience 1979.

I worked on this a little bit when I was a grad student at UCSC but didn't
implement the abstraction algorithm (a.k.a. lambda lifting).  Now, 32 years
later, I wrote it and 
the aim is to write a simple parser which can generate an abstract syntax tree
which is then rewritten to a combinator graph and translated to C code for
compilation and execution.

The program currently computes the factorial function by reducing a combinator
graph generated by the Haskell program `lift.hs`.

The input is an abstract syntax tree for fac = λx. if x=0 then 1 else x*fac(x-1):
```
Abs "x" (App (App (App (Var "cond") (App (App (Var "eq") (Var "x")) (Number 0))) (Number 1)) (App (App (Var "times") (Var "x")) (App (Var "fac") (App (App (Var "minus") (Var "x")) (Number 1)))))
```

The abstraction takes that and generates a combinator graph:
```
App (App S (App (App C (App (App B (Var "cond")) (App (App C (App (App B (Var "eq")) I)) (Number 0)))) (Number 1))) (App (App S (App (App B (Var "times")) I)) (App (App B (Var "fac")) (App (App C (App (App B (Var "minus")) I)) (Number 1))))
```

which is then simplified to
```
App (App S (App (App C (App (App B (Var "cond")) (App (App C (Var "eq")) (Number 0)))) (Number 1))) (App (App S (Var "times")) (App (App B (Var "fac")) (App (App C (Var "minus")) (Number 1))))
```

which is then printed as C-code:
```
Noderef facp = mkapply(mkapply(mkS(), mkapply(mkapply(mkC(), mkapply(mkapply(mkB(), mkCOND()), mkapply(mkapply(mkC(), mkEQ()), mknum(0)))), mknum(1))), mkapply(mkapply(mkS(), mkTIMES()), mkapply(mkapply(mkB(), fac), mkapply(mkapply(mkC(), mkMINUS()), mknum(1)))));
```

which I can insert in the `init` function in `sk.c` and compile and run and get a result.

My original paper listing from 1990 is scanned as a PDF file.
