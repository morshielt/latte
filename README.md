# latte


strukturę katalogów projektu[TODO:]
Latte x86 (AT&T) (stack machine) compiler with extensions:
- arrays
- structs
- objects
- objects with virtual methods.

Compiler was written in Haskell using standard library.

Additional requirements:
- `gcc-multilib` - 32-bit gcc libraries on 64-bit system

Usage (when `gcc-multilib` installed): 
```
make
./latc_x86 <file>
```

Usage on `students`:
```
make students
./latc_x86_students <file>
```

Compiler writes "OK\n" to stderr if it accepts the program and returns code 0,
otherwise it writes "ERROR\n" and according error message to stderr and returns code 1.

Extra assumptions:
- attribute (class field) name shadowing is forbidden
- reserved identifiers: "compareStrings_____", "concatStrings_____", "___iter", "___arr_ptr"
- reserved function's/method's names starting with "ret_"
- null cast has to be written without space: `(ClassNameOrArrayType)null`
- functions, methods and variables must have different names

