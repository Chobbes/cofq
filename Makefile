OPAMPKGS=coq coq-ext-lib coq-paco coq-ceres coq-flocq coq-mathcomp-ssreflect coq-simple-io dune menhir qcheck

.PHONY: opam update-submodules vellvm all cofq
all: vellvm quickchick cofq

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

.PHONY: quickcheck quickchick
quickcheck: quickchick

quickchick:
	make -C QuickChick

.PHONY: cofq-clean quickchick-clean vellvm-clean clean
cofq-clean:
	make -f CoqMakefile clean

vellvm-clean:
	make -C vellvm/src clean

quickchick-clean:
	make -C QuickChick clean

clean: cofq-clean quickchick-clean vellvm-clean
