# DISTRIBUTION STATEMENT A. Approved for public release. Distribution is unlimited.
#
# This material is based upon work supported by the Department of the Air Force under Air Force 
# Contract No. FA8702-15-D-0001. Any opinions, findings, conclusions or recommendations expressed 
# in this material are those of the author(s) and do not necessarily reflect the views of the 
# Department of the Air Force.
# 
# © 2019 Massachusetts Institute of Technology.
# 
# MIT Proprietary, Subject to FAR52.227-11 Patent Rights - Ownership by the contractor (May 2014)
# 
# The software/firmware is provided to you on an As-Is basis
# 
# Delivered to the U.S. Government with Unlimited Rights, as defined in DFARS Part 252.227-7013
# or 7014 (Feb 2014). Notwithstanding any copyright notice, U.S. Government rights in this work are
# defined by DFARS 252.227-7013 or DFARS 252.227-7014 as detailed above. Use of this work other than
#  as specifically authorized by the U.S. Government may violate any copyrights that exist in this work.

# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := CoqMakefile all lib por test-protos share-secret pgp secdns secvote p2p nsproto timings

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

# # frap:
# # 	$(MAKE) -C frap lib

# protocols/*.vo: CoqMakefile
# 	echo "Building " $@
# 	$(MAKE) -f CoqMakefile pretty-timed TGTS=$@

lib: CoqMakefile
	$(MAKE) -f CoqMakefile KeyManagement/AdversarySafety.vo

por: CoqMakefile
	$(eval TS := protocols/PartialOrderReduction.vo)
	$(MAKE) -f CoqMakefile pretty-timed TGTS=$(TS)

test-protos: CoqMakefile
	$(eval TS := "protocols/ExampleProtocolsAutomated.vo protocols/GenProto.vo protocols/GenProtoSS.vo")
	$(MAKE) -f CoqMakefile pretty-timed TGTS=$(TS)

sharesecret: CoqMakefile
	$(eval TS := "protocols/ShareSecretProtocol2.vo protocols/ShareSecretProtocol2SS.vo")
	$(MAKE) -f CoqMakefile pretty-timed TGTS=$(TS)

pgp: CoqMakefile
	$(eval TS := "protocols/PGP.vo protocols/PGPSS.vo")
	$(MAKE) -f CoqMakefile pretty-timed TGTS=$(TS)

sharesecretsym: CoqMakefile
	$(eval TS := "protocols/ShareSecretSymmetricEncProtocol.vo protocols/ShareSecretSymmetricEncProtocolSS.vo")
	$(MAKE) -f CoqMakefile pretty-timed TGTS=$(TS)

secdns: CoqMakefile
	$(eval TS := "protocols/SecureDNS.vo protocols/SecureDNSSS.vo")
	$(MAKE) -f CoqMakefile pretty-timed TGTS=$(TS)

secvote: CoqMakefile
	$(eval TS := "protocols/SecureVoting.vo protocols/AvgSalary.vo")
	$(MAKE) -f CoqMakefile pretty-timed TGTS=$(TS)

p2p: CoqMakefile
	$(eval TS := "protocols/P2P.vo")
	$(MAKE) -f CoqMakefile pretty-timed TGTS=$(TS)

p2pv2: CoqMakefile
	$(eval TS := "protocols/P2Pv2.vo")
	$(MAKE) -f CoqMakefile pretty-timed TGTS=$(TS)

nsproto: CoqMakefile
	$(eval TS := protocols/NeedhamSchroeder.vo)
	$(MAKE) -f CoqMakefile $(TS)

timings: CoqMakefile
	echo "Timings" $@
	$(eval TS := protocols/ShareSecretProtocol.vo protocols/ShareSecretProtocol2.vo)
	$(MAKE) -f CoqMakefile pretty-timed TGTS=$(TS)

# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true
