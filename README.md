# latte


## Gramatyka
Gramatyka to nieco zmodyfikowana gramatyka języka *Latte*.

W gramatyce występuje konflikt:
wyrażenie `if (cond1) f1(); if (cond2) f2(); else g();` jest parsowane tak, że `else` należy do __drugiego__ `if`.


./bnfc -m Latte.cf
make
alex --ghc LexLatte.x
happy --ghc --coerce --array --info ParLatte.y
ghc --make TestLatte.hs -o TestLatte


Predefiniowane funkcje
Są dostępne predefiniowane funkcje:

void printInt(int)
void printString(string)
void error()
int readInt()
string readString()

Funkcja error wypisuje runtime error i kończy wykonywanie programu.

Funkcja readString wczytuje jedną linię z wejścia i daje ją jako wynik. 
