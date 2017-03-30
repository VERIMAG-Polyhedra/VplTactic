# requires: coq8.6

.PHONY: clean tactic cacheclean test archclean install uninstall

MLTACTICOPT:=-rectypes -thread -package vpl -linkpkg

test: tactic
	$(MAKE) -j -f tactic.mk "OPT:=-opt"

tactic: tactic.mk
	$(MAKE) -j -f tactic.mk src/vpltactics.cmx "OPT:=-opt" "CAMLC:=ocamlfind ocamlc -c $(MLTACTICOPT)" "CAMLOPTC:=ocamlfind ocamlopt -c $(MLTACTICOPT)" "CAMLLINK:=ocamlfind ocamlc $(MLTACTICOPT)" "CAMLOPTLINK:=ocamlfind ocamlopt $(MLTACTICOPT)"
	$(MAKE) -j -f tactic.mk src/reification.cmx "OPT:=-opt" "CAMLC:=ocamlfind ocamlc -c $(MLTACTICOPT)" "CAMLOPTC:=ocamlfind ocamlopt -c $(MLTACTICOPT)" "CAMLLINK:=ocamlfind ocamlc $(MLTACTICOPT)" "CAMLOPTLINK:=ocamlfind ocamlopt $(MLTACTICOPT)"
	$(MAKE) -j -f tactic.mk src/vpl_plugin.cmxa "OPT:=-opt" 
	$(MAKE) -j -f tactic.mk "OPT:=-opt" "CAMLC:=ocamlfind ocamlc -c $(MLTACTICOPT)" "CAMLOPTC:=ocamlfind ocamlopt -c $(MLTACTICOPT)" "CAMLLINK:=ocamlfind ocamlc $(MLTACTICOPT)" "CAMLOPTLINK:=ocamlfind ocamlopt $(MLTACTICOPT)" theories/Tactic.vo

tactic.mk: _CoqProject
	coq_makefile -f _CoqProject -o tactic.mk

install: tactic
	$(MAKE) -f tactic.mk install

uninstall: tactic.mk
	$(MAKE) -f tactic.mk uninstall || echo "skip last errors..."

coqide:
	@echo "coqide -R theories VplTactic -I src"

cacheclean:
	rm -rf */.*.aux .*.cache */*~ *~

clean: tactic.mk cacheclean
	$(MAKE) -f tactic.mk clean

archclean: clean
	rm -f tactic.mk
