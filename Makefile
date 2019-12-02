.PHONY: all coq frap

all: coq

include Makefile.coq.conf

VOFILES = $(COQMF_VFILES:.v=.vo)

frap:
	$(MAKE) -C frap lib

coq: Makefile.coq frap
	$(MAKE) -f Makefile.coq $(filter-out protocols%,$(VOFILES))

protocols: coq
	$(MAKE) -f Makefile.coq $(filter protocols%,$(VOFILES))

pingpong: coq
	$(MAKE) -f Makefile.coq protocols/EncPingProtocol.vo

simpleping: coq
	$(MAKE) -f Makefile.coq protocols/SimplePingProtocol.vo

Makefile.coq.conf: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

Makefile.coq: Makefile _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
