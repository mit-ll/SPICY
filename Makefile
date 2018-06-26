.PHONY: coq clean

COQC=coqc -q -R ../frap Frap

coq:
	$(COQC) inductive2

clean:
	rm -f *.vo *.glob
