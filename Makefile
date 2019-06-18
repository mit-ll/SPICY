.PHONY: all coq frap

all: coq

frap:
	$(MAKE) -C frap lib

coq: Makefile.coq frap
	$(MAKE) -f Makefile.coq

pingpong: coq
	$(MAKE) -f Makefile.coq protocols/EncPingProtocol.vo

Makefile.coq: Makefile _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
