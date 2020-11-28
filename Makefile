all:
	# ghc Main -iparser:interpret:typecheck -o interpreter
	ghc src/Main -isrc/parser -o complier
