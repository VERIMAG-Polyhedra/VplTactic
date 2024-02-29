# requires: coq8.9

.PHONY: clean tactic cacheclean test archclean install uninstall

test: tactic
	$(MAKE) -f tactic.mk

tactic: tactic.mk
	$(MAKE) -f tactic.mk theories/Tactic.vo

tactic.mk: _CoqProject
	coq_makefile -f _CoqProject -o tactic.mk

install: tactic
	$(MAKE) -f tactic.mk install

uninstall: tactic.mk
	$(MAKE) -f tactic.mk uninstall || echo "skip last errors..."

coqide:
	@echo "coqide"

cacheclean:
	rm -rf */.*.aux .*.cache */*~ *~

clean: tactic.mk cacheclean
	$(MAKE) -f tactic.mk clean

archclean: clean
	rm -f tactic.mk
