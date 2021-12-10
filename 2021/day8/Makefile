include /home/mark/.opam/4.12.1/lib/fstar/ml/Makefile.include
FSTAR=fstar.exe

part1: Part1

part2: Part2

programs = Part1 Part2 ExampleBug

$(programs): %: %.fst out
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --extract '$@' $< --record_hints
	$(OCAMLOPT) out/$@.ml -o out/$@
	./out/$@

out:
	mkdir -p out
