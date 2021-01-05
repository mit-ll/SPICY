# Secure Protocols Implemented CorrectlY (SPICY)

Some witty project description.

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

opam switch create coq-<ver> ocaml-base-compiler.4.08.1

opam install coq.<ver>
opam pin add coq <ver>
```

### Compiling Project

```bash
git clone ssh://git@github.mit.edu/mitll-crows/key-management-model
cd key-management-model

# Pull in submodules
git submodule update --init --recursive

make
```

## Disclaimer

DISTRIBUTION STATEMENT A. Approved for public release. Distribution is unlimited.

© 2019-2021 Massachusetts Institute of Technology.
* MIT Proprietary, Subject to FAR52.227-11 Patent Rights - Ownership by the Contractor (May 2014)
* SPDX-License-Identifier: MIT

This material is based upon work supported by the Department of the Air Force under Air Force Contract No. FA8702-15-D-0001. Any opinions, findings, conclusions or recommendations expressed in this material are those of the author(s) and do not necessarily reflect the views of the Department of the Air Force.

The software/firmware is provided to you on an As-Is basis
