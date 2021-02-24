COQMAKEFILE?=$(COQBIN)coq_makefile
build:
	$(COQMAKEFILE) -f _CoqProject -o Makefile.coq
	$(MAKE) -f Makefile.coq

install:
	$(MAKE) -f Makefile.coq install

clean:
	$(MAKE) -f Makefile.coq clean

