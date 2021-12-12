include /home/mark/.opam/4.12.1/lib/fstar/ml/Makefile.include
FSTAR=fstar.exe

part1: Part1

part2: Part2

programs = Part1 Part2

$(programs): %: %.fst out
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --extract '$@' $< --record_hints
	$(OCAMLOPT) out/$@.ml -o out/$@
	./out/$@

OCAML_INCLUDE_PATHS=-I ./out

Demo: Demo.fst out
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --extract 'Demo +Aki' Demo.fst --record_hints --include ../../lib
	$(OCAMLOPT) $(OCAML_INCLUDE_PATHS) out/Aki.ml out/Demo.ml -o out/Demo 
	./out/Demo

out:
	mkdir -p out
