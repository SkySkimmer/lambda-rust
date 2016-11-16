%: Makefile.coq phony
	+@make -f Makefile.coq $@

# Compile this project
all: Makefile.coq
	+@make -f Makefile.coq all

clean: Makefile.coq
	+@make -f Makefile.coq clean
	rm -f Makefile.coq

Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject | sed 's/$$(COQCHK) $$(COQCHKFLAGS) $$(COQLIBS)/$$(COQCHK) $$(COQCHKFLAGS) $$(subst -Q,-R,$$(COQLIBS))/' > Makefile.coq

# Use local Iris dependency
iris-local:
	git submodule update --init iris # If not initialized, then initialize; If not updated with this remote, then update
	ln -nsf iris iris-enabled # If not linked, then link
	+make -C iris -f Makefile # If not built, then build

# Use system-installed Iris dependency
iris-system: clean
	rm -f iris-enabled

_CoqProject: ;

Makefile: ;

phony: ;

.PHONY: all clean phony iris-local iris-system
