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
KNOWNTARGETS := CoqMakefile lib por exampleprotos sharesecret protocols

# KNOWNFILES will not get implicit targets from the final rule, and so
# depending on them won't invoke the submake
# Warning: These files get declared as PHONY, so any targets depending
# on them always get rebuilt
KNOWNFILES   := Makefile _CoqProject

.DEFAULT_GOAL := invoke-coqmakefile

CoqMakefile: Makefile _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o CoqMakefile

invoke-coqmakefile: CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-coqmakefile $(KNOWNFILES)

####################################################################
##                      Your targets here                         ##
####################################################################

# # frap:
# # 	$(MAKE) -C frap lib

lib: CoqMakefile
	$(MAKE) -f CoqMakefile KeyManagement/AdversarySafety.vo

por: CoqMakefile
	$(MAKE) -f CoqMakefile protocols/PORExtended.vo

exampleprotos: CoqMakefile
	$(MAKE) -f CoqMakefile protocols/ExampleProtocolsAutomated.vo

sharesecret: CoqMakefile
	$(MAKE) -f CoqMakefile protocols/ShareSecretProtocol.vo

secdns: CoqMakefile
	$(MAKE) -f CoqMakefile pretty-timed TGTS="protocols/SecureDNS.vo"

protocols: exampleprotos sharesecret

timings: CoqMakefile
	$(MAKE) -f CoqMakefile pretty-timed TGTS="protocols/ShareSecretProtocol.vo protocols/ShareSecretProtocol2.vo"


# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true
