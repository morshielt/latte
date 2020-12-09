all:
	# ghc Main -iparser:interpret:typecheck -o interpreter
	# TODO: bad008.lat bad012.lat bad021.lat bad024.lat bad025.lat
	ghc -Werror src/Main -isrc/parser:src/static_analysis -o complier
