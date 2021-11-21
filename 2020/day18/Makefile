include /home/mark/.opam/4.12.1/lib/fstar/ml/Makefile.include
FSTAR=fstar.exe

part1: Part1

part2: Part2

programs = Part1 Part2

EXTRACT_LIBS='+Parser +Suffixes'
OCAML_INCLUDE_PATHS=-I ./out

$(programs): %: %.fst out
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --extract '$@ +Parser +Suffixes' $< --record_hints --include ../../lib/
	$(OCAMLOPT) -o out/$@ $(OCAML_INCLUDE_PATHS) out/Suffixes.ml out/Parser.ml out/$@.ml
	./out/$@

out:
	mkdir -p out
