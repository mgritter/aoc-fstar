include /home/mark/.opam/4.12.1/lib/fstar/ml/Makefile.include
FSTAR=fstar.exe

part1: Part1

part2: Part2

programs = Part1 Part2

$(programs): %: %.fst out
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --include ../../lib --odir out --codegen OCaml --extract '$@ +LeftistHeap' $< --record_hints --use_hints --cache_checked_modules
	$(OCAMLOPT) out/LeftistHeap.ml out/$@.ml -o out/$@ -I out
	./out/$@

out:
	mkdir -p out
