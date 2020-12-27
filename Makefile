all:
	ghc -Werror src/Main -isrc/parser:src/static_analysis:src/compiler -o latc

clean:
	rm src/*.o src/*.hi src/parser/*.hi src/parser/*.o src/static_analysis/*.hi src/static_analysis/*.o src/compiler/*.hi src/compiler/*.o
