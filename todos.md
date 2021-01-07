-- DONE: for (int i : arr) i = 5; -- czy to w ogóle se można takie przypisania?
-- DONE: jaki jest default decl klasy rekurencyjnej? (list atrybutem list) null chyba nie?

./bnfc -m Latte.cf 
make 
alex --ghc LexLatte.x happy --ghc --coerce --array --info ParLatte.y 
ghc --make TestLatte.hs -o TestLatte
