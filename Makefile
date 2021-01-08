#
# © 2019 Massachusetts Institute of Technology.
# MIT Proprietary, Subject to FAR52.227-11 Patent Rights - Ownership by the Contractor (May 2014)
# SPDX-License-Identifier: MIT
# 

# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := CoqMakefile all lib por test-protos share-secret pgp secdns aggregate p2p paper-fast

# KNOWNFILES will not get implicit targets from the final rule, and so
# depending on them won't invoke the submake
# Warning: These files get declared as PHONY, so any targets depending
# on them always get rebuilt
KNOWNFILES   := Makefile _CoqProject

.DEFAULT_GOAL := invoke-coqmakefile

CoqMakefile: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o CoqMakefile

invoke-coqmakefile: CoqMakefile
	echo "Invoke makefile: " $(MAKECMDGOALS)
	$(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-coqmakefile $(KNOWNFILES)

####################################################################
##                      Your targets here                         ##
####################################################################

lib: CoqMakefile
	$(MAKE) -f CoqMakefile src/AdversarySafety.vo \
			       src/ModelCheck/PartialOrderReduction.vo \
			       src/ModelCheck/ProtocolAutomation.vo

por: CoqMakefile
	$(eval TS := src/ModelCheck/PartialOrderReduction.vo)
	$(MAKE) -f CoqMakefile pretty-timed TGTS=$(TS)

test-protos: CoqMakefile
	$(eval TS := "protocols/ExampleProtocolsAutomated.vo protocols/GenProto.vo protocols/GenProtoSS.vo")
	$(MAKE) -f CoqMakefile pretty-timed TGTS=$(TS)

sharesecret: CoqMakefile
	$(eval TS := "protocols/ShareSecretProtocolTS.vo protocols/ShareSecretProtocolSS.vo")
	$(MAKE) -f CoqMakefile pretty-timed TGTS=$(TS)

sharesecretsym: CoqMakefile
	$(eval TS := "protocols/ShareSecretProtocolSymmetricEncTS.vo protocols/ShareSecretProtocolSymmetricEncSS.vo")
	$(MAKE) -f CoqMakefile pretty-timed TGTS=$(TS)

pgp: CoqMakefile
	$(eval TS := "protocols/PGPTS.vo protocols/PGPSS.vo")
	$(MAKE) -f CoqMakefile pretty-timed TGTS=$(TS)

secdns: CoqMakefile
	$(eval TS := "protocols/SecureDNSTS.vo protocols/SecureDNSSS.vo")
	$(MAKE) -f CoqMakefile pretty-timed TGTS=$(TS)

aggregate: CoqMakefile
	$(eval TS := "protocols/AvgSalary.vo")
	$(MAKE) -f CoqMakefile pretty-timed TGTS=$(TS)

p2p: CoqMakefile
	$(eval TS := "protocols/P2P.vo")
	$(MAKE) -f CoqMakefile pretty-timed TGTS=$(TS)

paper-fast: CoqMakefile
	$(eval TS :="protocols/ShareSecretProtocolSS.vo protocols/ShareSecretProtocolSymmetricEncSS.vo protocols/PGPSS.vo protocols/SecureDNSSS.vo")
	$(MAKE) -f CoqMakefile pretty-timed TGTS=$(TS)


# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true
