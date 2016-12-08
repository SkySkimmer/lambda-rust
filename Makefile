# Process flags
ifeq ($(Y), 1)
	YFLAG=-y
endif

# Determine Coq version
COQ_VERSION=$(shell coqc --version | egrep -o 'version 8.[0-9]' | egrep -o '8.[0-9]')
COQ_MAKEFILE_FLAGS ?=

ifeq ($(COQ_VERSION), 8.6)
	COQ_MAKEFILE_FLAGS += -arg -w -arg -notation-overridden,-redundant-canonical-projection
endif

# Forward most targets to Coq makefile (with some trick to make this phony)
%: Makefile.coq phony
	+@make -f Makefile.coq $@

all: Makefile.coq
	+@make -f Makefile.coq all

clean: Makefile.coq
	+@make -f Makefile.coq clean
	find \( -name "*.v.d" -o -name "*.vo" -o -name "*.aux" -o -name "*.cache" -o -name "*.glob" -o -name "*.vio" \) -print -delete
	rm -f Makefile.coq

# Create Coq Makefile
Makefile.coq: _CoqProject Makefile
	@# we want to pass the correct name to coq_makefile or it will be confused.
	coq_makefile $(COQ_MAKEFILE_FLAGS) -f _CoqProject -o Makefile.coq
	mv Makefile.coq Makefile.coq.tmp
	@# The sed script is for Coq 8.5 only, it fixes 'make verify'.
	@# The awk script fixes 'make uninstall'.
	sed 's/$$(COQCHK) $$(COQCHKFLAGS) $$(COQLIBS)/$$(COQCHK) $$(COQCHKFLAGS) $$(subst -Q,-R,$$(COQLIBS))/' < Makefile.coq.tmp \
	  | awk '/^uninstall:/{print "uninstall:";print "\tif [ -d \"$$(DSTROOT)\"$$(COQLIBINSTALL)/iris/ ]; then find \"$$(DSTROOT)\"$$(COQLIBINSTALL)/iris/ -name \"*.vo\" -print -delete; fi";getline;next}1' > Makefile.coq
	rm Makefile.coq.tmp

# Install build-dependencies
build-dep:
	build/opam-pins.sh < opam.pins
	opam upgrade $(YFLAG) # it is not nice that we upgrade *all* packages here, but I found no nice way to upgrade only those that we pinned
	opam pin add coq-lambda-rust "$$(pwd)#HEAD" -k git -n -y
	opam install coq-lambda-rust --deps-only $(YFLAG)
	opam pin remove coq-lambda-rust

# some fiels that do *not* need to be forwarded to Makefile.coq
Makefile: ;
_CoqProject: ;

# Phony targets (i.e. targets that should be run no matter the timestamps of the involved files)
phony: ;
.PHONY: all clean phony
