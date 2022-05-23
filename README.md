# Secure Protocols Implemented CorrectlY (SPICY)

This repository contains the main developments of the SPICY protocol development and specification tool.

## Repository Layout

This repository has three top-level directories:
* Frap -- we bootstrapped the project by using some developments from the FRAP library
* src -- core library code, including Domain Specific Languages (DSLs), their semantics, and the safety theorem
* protocols -- several test protocols proven correct

Some good places to start to get a feel for the formalized languages and main safety result:

* src/IdealWorld.v -- formalization of the Ideal World language.
* src/RealWorld.v -- formalization of the Real World language.
* src/Simulation.v -- development of our simulation statements between the Ideal and Real worlds (the actual simulation definitions can be found in the "Simulation" section).  Also included here is the predicate which encodes the "best practice rules", called `honest_cmds_safe` (leveraging `next_cmd_safe` for most of the actual work).
* src/AdversarySafety.v -- the main theorems and lemmas stating the safety result.

The main safety results within AdversarySafety warrant some further discussion.
The last theorem (`refines_could_generate`) is the statement that if a Real
World protocol refines an Ideal World protocol, then traces in the Real World
can be reproduced in the Ideal World. A few hundred lines up from there, in
`refines_ok_with_adversary` is the main lemma supporting
`refines_could_generate` where we show that, starting from a refinement
condition in a universe with no adversary, we can inject arbitrary adversary
code and obtain a refinement condition within this new universe.

Using the above library code, we have verified several exemplar protocols.

* protocols/PGP.v (protocol impl) and protocols/Verification/PGPSecure.v (correctness proof) -- describes a secret sharing protocol inspired by the PGP protocol.
* protocols/SecureDNS.v (protocol impl) and protocols/Verification/SecureDNSSecure.v (correctness proof) -- describes a protocol similar in spirit to (but much simplified) Daniel Bernstein's DNSCurve for encrypted DNS.
* protocols/AvgSalary.v and protocols/Verification/AvgSalarySecure.v -- describes a simple aggregation service, interesting because it involves more than two parties.
* protocols/NetAuth.v and protocols/Verification/NetAuthSecure.v -- describes a network authentication protocol by a trusted third party showing an alternative way of bootstrapping trusted keys

Finally, it may not be obvious how the protocol proofs link back to the main correctness result (`refines_could_generate`).  Note that the protocol proofs are proofs that each protocol implementation, along with its starting state (pre-shared keys, channels, etc.) conforms to a module type (`AutomatedSafeProtocolSS`).  That module type is enough to link the proofs to the overall safety result.  If you look in `src/ModelCheck/SilentStepElimination`, you find towards the end that protocols implementing `AutomatedSafeProtocolSS` can be proven to demonstrate `protocol_with_adversary_could_generate_spec`, which states the same trace inclusion condition as the main result.

## Setup

Setup notes for future me.

### Installing coq

Make sure coq is installed an on the path.  I find it convenient to
install via opam, using switches.  Some quick notes on how to do that:

The *first* time you use opam, you need to set up your environment.

```bash
opam init

opam repo add coq-released https://coq.inria.fr/opam/released --set-default
```

Now, whenever you want to install a new version, just do:

```bash
opam update

opam switch create coq-8.13.2 ocaml-base-compiler.4.11.1

opam install coq.8.13.2
opam pin add coq 8.13.2
```

### Compiling Project

```bash
git clone <url>

# Pull in submodules
git submodule update --init --recursive

# Compiles the faster paper example protocol
make paper-fast

# Compiles all paper example protocols
make paper-all
```

## Disclaimer

DISTRIBUTION STATEMENT A. Approved for public release. Distribution is unlimited.

© 2019-2021 Massachusetts Institute of Technology.
* MIT Proprietary, Subject to FAR52.227-11 Patent Rights - Ownership by the Contractor (May 2014)
* SPDX-License-Identifier: MIT

This material is based upon work supported by the Department of the Air Force under Air Force Contract No. FA8702-15-D-0001. Any opinions, findings, conclusions or recommendations expressed in this material are those of the author(s) and do not necessarily reflect the views of the Department of the Air Force.

The software/firmware is provided to you on an As-Is basis
