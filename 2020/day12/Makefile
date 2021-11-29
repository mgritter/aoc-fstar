include /home/mark/.opam/4.12.1/lib/fstar/ml/Makefile.include
FSTAR=fstar.exe

part1: Part1

part2: Part2

part3: Part3

programs = Part1 Part2

$(programs): %: %.fst out
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --extract '$@' $< --record_hints
	$(OCAMLOPT) out/$@.ml -o out/$@
	./out/$@

Part3: Part3.fst BoatEffect.fst Boat.fsti out out/Boat.ml
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml --extract '$@ +BoatEffect' $< --record_hints
	$(OCAMLOPT) out/BoatEffect.ml out/Boat.ml out/$@.ml -o out/$@ -I out
	./out/$@

out:
	mkdir -p out

out/Boat.ml:
	cp Boat.ml out/Boat.ml
