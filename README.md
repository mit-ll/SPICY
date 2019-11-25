# Key Management Formalization

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

opam switch create coq-<ver> ocaml-base-compiler.4.05.0

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
