OPAMPKGS=coq coq-ext-lib coq-paco coq-ceres coq-flocq dune menhir qcheck

all: vellvm
	coqc SystemF.v

.PHONY: opam update-submodules vellvm
opam:
	opam install $(OPAMPKGS)

update-submodules:
	git submodule update --init --recursive

vellvm: opam
	make -C vellvm/src
