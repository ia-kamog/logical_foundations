.PHONY: all
all: CoqMakefile
	make -f CoqMakefile
CoqMakefile: _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile
.PHONY: clean
clean:
	test -f CoqMakefile && make -f CoqMakefile clean
	-rm -f CoqMakefile CoqMakefile.conf .*.aux
