include /home/mark/.opam/4.12.1/lib/fstar/ml/Makefile.include
FSTAR=fstar.exe

part1: out Part1.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --extract 'Part1' Part1.fst --record_hints
	$(OCAMLOPT) out/Part1.ml -o part1
	./part1

part2: out Part2.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --extract 'Part2' Part2.fst --record_hints
	$(OCAMLOPT) out/Part2.ml -o part2
	./part2

out:
	mkdir -p out
