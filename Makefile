all:
	ghc -Werror src/Main -isrc/parser:src/static_analysis -o complier
