#
# © 2019 Massachusetts Institute of Technology.
# MIT Proprietary, Subject to FAR52.227-11 Patent Rights - Ownership by the Contractor (May 2014)
# SPDX-License-Identifier: MIT
# 

# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := CoqMakefile #all lib por test-protos share-secret pgp secdns aggregate p2p paper-fast

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
			       src/ModelCheck/InvariantSearch.vo

# test-protos: lib
# 	$(eval TS := "protocols/Verification/GenProtoSecure.vo")
# 	$(MAKE) -f CoqMakefile pretty-timed TGTS=$(TS)

paper-fast: lib
	$(eval TS :="protocols/Verification/ShareSecretProtocolSymmetricEncSecure.vo protocols/Verification/PGPSecure.vo protocols/Verification/SecureDNSSecure.vo")
	$(MAKE) -f CoqMakefile pretty-timed TGTS=$(TS)

paper-all: lib
	$(eval TS :="protocols/Verification/ShareSecretProtocolSymmetricEncSecure.vo protocols/Verification/PGPSecure.vo protocols/Verification/SecureDNSSecure.vo protocols/Verification/AvgSalarySecure.vo protocols/Verification/NetAuthSecure.vo")
	$(MAKE) -f CoqMakefile pretty-timed TGTS=$(TS)

# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true
