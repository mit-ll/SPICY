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

### Example Protocols

Using the above library code, we have verified several exemplar protocols.

* protocols/PGP.v (protocol impl) and protocols/Verification/PGPSecure.v (correctness proof) -- describes a secret sharing protocol inspired by the PGP protocol.
* protocols/SecureDNS.v (protocol impl) and protocols/Verification/SecureDNSSecure.v (correctness proof) -- describes a protocol similar in spirit to (but much simplified) Daniel Bernstein's DNSCurve for encrypted DNS.
* protocols/AvgSalary.v and protocols/Verification/AvgSalarySecure.v -- describes a simple aggregation service, interesting because it involves more than two parties.
* protocols/NetAuth.v and protocols/Verification/NetAuthSecure.v -- describes a network authentication protocol by a trusted third party showing an alternative way of bootstrapping trusted keys

In the paper, we describe a relation which allows us to step-by-step explore the possible real world protocol executions, and check that they adhere to the ideal world specifications.  The model checking procedure is encoded in `src/ModelCheck/SafeProtocol.v`.  There, we encode a module signature `AutomatedSafeProtocol` which describes the transition system that is explored by the model checker.  It is comprised of the initial real and ideal world universe states, some proofs that the real world starts in an okay state (these predicates `U_good` and `universe_starts_safe` aren't anything fancy, but make sure that the conditions needed to start the model checking procedure do so in such a way that 'universe goodness' can be preserved -- these conditions are satisfied, for example, if honest party message queues start empty, hidden universe state that the operational semantics checks start empty, and only honest keys are pre-provisioned).  Last, the module signature contains a proof obligation (which is the job of the model checker to explore) that the transition system satisfies three predicates at each step (`safety`, `alignment`, and `returns_align`).  The first predicate is a repackaging of `honest_cmds_safe` mentioned earlier.  The second and third predicates are simply checks that the model checking is proceeding according to rules of the simulation statement described in Section III.C of the paper.  Finally, the functor `ProtocolSimulates` proves that any protocol which adheres to the `AutomatedSafeProtocol` module signature is adversary safe (Theorem `protocol_with_adversary_could_generate_spec`) via application of the main development theorem `refines_could_generate`.

In practice, we don't directly use the above module signature or transition system to prove protocol correctness.  As noted in the paper, it is always safe for adversaries to take silent steps eagerly, thus greatly reducing the necessary state space exploration.  However, we need to prove the soundness of this argument.  To do so, we create a new module signature `AutomatedSafeProtocolSS` which defines this aggressive silent-stepping transition system.  It basically the same starting conditions as `AutomatedSafeProtocol`.  Additionally, it adds a few syntactic predicates over the real world protocol implementations (`finitelyRuns`, `typechecks`, and `summarizable`).  The first two predicates check that the number of protocol execution steps are bounded by some number and the protocol passes certain syntactic safety checks (which encompass most of the `honest_cmds_safe` checks), respectively.  The third condition is currently a no-op and was put in place for full partial order reduction analysis which is currently not implemented.  Finally, the `safe_invariant` theorem is the check that at every state explored by the transition system, the predicates `no_resends_U`, `alignment`, and `returns_align` are satisfied.  These only differ from `AutomatedSafeProtocol` in the first predicate (remember, the last two simply ensure that the transition steps follow the prescribed rules).  In this transition system, the syntactic `typechecks` check along with `no_resends_U` prove the equivalent safety condition as `safety` does in `AutomatedSafeProtocol`.  We think this is pretty cool -- the best practice rules can be transformed into a fairly simple typechecker, with the exception of one condition (this condition is the check that honest parties do not resend messages, and couldn't easily be fit into the typechecking style)!  We then go onto show that `AutomatedSafeProtocolSS` can also be lifted into the `ProtocolSimulates` functor, and prove the final theorem `refines_could_generate`.

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

opam switch create coq-8.15.1 ocaml-base-compiler.4.13.1

opam install coq.8.15.1
opam pin add coq 8.15.1
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
