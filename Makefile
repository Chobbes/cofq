OPAMPKGS=coq coq-ext-lib coq-paco coq-ceres coq-flocq dune menhir qcheck

.PHONY: opam update-submodules vellvm all cofq
all: vellvm cofq

cofq: CoqMakefile
	make -f CoqMakefile

CoqMakefile:
	coq_makefile -f _CoqProject -o CoqMakefile

opam:
	opam install $(OPAMPKGS)

update-submodules:
	git submodule update --init --recursive

vellvm: opam
	make -C vellvm/src
