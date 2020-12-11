# latte

Latte Frontend with extensions:
    - arrays
    - structs
    - objects with virtual methods.
<!-- 
## Gramatyka
Gramatyka to nieco zmodyfikowana gramatyka języka *Latte*.

W gramatyce występuje konflikt:
wyrażenie `if (cond1) f1(); if (cond2) f2(); else g();` jest parsowane tak, że `else` należy do __drugiego__ `if`. -->

TODO: 2gi shift reduce co to jest z nim D:

Some arbitrary decisions:





TODO: compiler -> ./latc




./bnfc -m Latte.cf
make
alex --ghc LexLatte.x
happy --ghc --coerce --array --info ParLatte.y
ghc --make TestLatte.hs -o TestLatte



-- TODO: posprawdzać jak wyglądają error message

-- TODO: to chyba też już nie w typechecku
-- int[][] arr = new int[][20];
-- arr[1] = 5; -- TODO: co tu w ogóle można przypisać? tablicę odp. długości czy nic czy co????
-- TODO: jak się odwołuję poza tablicę, ale to raczej już później, bo w typechecku chyba nie mogę?
-- TODO: for (int i : arr) i = 5; -- czy to w ogóle se można takie przypisania?
-- TODO: jaki jest default decl klasy rekurencyjnej? (list atrybutem list) null chyba nie?


-- TODO: piękne error messages xD
 Not in scope:

src/static_analysis/SAStmts.hs:69:22: error:
    • Couldn't match type ‘Stmt’ with ‘[Stmt]’
      Expected type: [[Stmt]]
        Actual type: [Stmt]
    • In the third argument of ‘foldM’, namely ‘ss’
      In a stmt of a 'do' block: foldM go env ss
      In the expression:
        do { env <- ask;
             foldM go env ss }

