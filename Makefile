%: Makefile.coq phony
	+@make -f Makefile.coq $@

all: Makefile.coq
	+@make -f Makefile.coq all

clean: Makefile.coq
	+@make -f Makefile.coq clean
	rm -f Makefile.coq

Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject | sed 's/$$(COQCHK) $$(COQCHKFLAGS) $$(COQLIBS)/$$(COQCHK) $$(COQCHKFLAGS) $$(subst -Q,-R,$$(COQLIBS))/' > Makefile.coq

iris-local: clean
	git submodule update --init iris
	ln -nsf iris iris-enabled
	+make -C iris -f Makefile

iris-system: clean
	rm -f iris-enabled

_CoqProject: ;

Makefile: ;

phony: ;

.PHONY: all clean phony iris-local iris-system
