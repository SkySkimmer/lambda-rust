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

build-dep:
	cat opam.pins | build/opam-pins.sh
	opam pin add coq-lambda-rust "$$(pwd)#HEAD" -k git -y -n
	opam install coq-lambda-rust --deps-only -y

_CoqProject: ;

Makefile: ;

phony: ;

.PHONY: all clean phony iris-local iris-system
