.PHONY: all coq frap

all: coq

frap:
	$(MAKE) -C frap

coq: Makefile.coq frap
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
