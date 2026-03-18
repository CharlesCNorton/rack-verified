COQMAKEFILE := rocq makefile -f _CoqProject

all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	$(COQMAKEFILE) -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf

.PHONY: all clean
