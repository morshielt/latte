# latte

Latte Frontend with extensions:
    - arrays
    - structs
    - objects with virtual methods.


Usage: 
```
make
./latc <file>
```
gcc -m32 ../lib/runtime.o test1.s -o test1


Compiler writes "OK\n" to stderr if it accepts the program and returns code 0,
otherwise it writes "ERROR\n" and according error message to stderr and returns code 1.


