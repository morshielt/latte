all:
	gcc -m32 -c lib/runtime.c -o lib/runtime.o
	ghc -Werror src/Main -isrc/parser:src/static_analysis:src/compiler -o compiler

clean:
	rm src/*.o src/*.hi src/parser/*.hi src/parser/*.o src/static_analysis/*.hi src/static_analysis/*.o src/compiler/*.hi src/compiler/*.o

students:
	gcc -m32 -g -D_GNU_SOURCE -c -O lib/runtime.c -o lib/runtime.o
	ghc -Werror src/Main -isrc/parser:src/static_analysis:src/compiler -o compiler
