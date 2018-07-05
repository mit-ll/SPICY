.PHONY: coq clean

COQC=coqc -q -R ../frap Frap

coq:
	$(COQC) channels
clean:
	rm -f *.vo *.glob
