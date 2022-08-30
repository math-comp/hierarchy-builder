[![Actions Status](https://github.com/math-comp/hierarchy-builder/workflows/CI/badge.svg)](https://github.com/math-comp/hierarchy-builder/actions)
[![project chat](https://img.shields.io/badge/zulip-join_chat-brightgreen.svg)](https://coq.zulipchat.com/#narrow/stream/237868-Hierarchy-Buidlder)

# Hierarchy Builder

Hierarchy Builder (HB) provides high level commands to declare a hierarchy of algebraic structure
(or interfaces if you prefer the glossary of computer science) for the Coq system.

Given a structure one can develop its theory, and that theory becomes automatically applicable to
all the examples of the structure. One can also declare alternative interfaces, for convenience
or backward compatibility, and provide glue code linking these interfaces to the structures part of
the hierarchy.

HB commands compile down to Coq modules, sections, records, coercions, canonical structure instances
and notations following the *packed classes* discipline which is at the core of the [Mathematical
Components](https://github.com/math-comp/math-comp) library. All that complexity is hidden behind
a few concepts and a few declarative Coq commands.

## Example

```coq
From HB Require Import structures.
From Coq Require Import ssreflect ZArith.

HB.mixin Record IsAddComoid A := {
  zero : A;
  add : A -> A -> A;
  addrA : forall x y z, add x (add y z) = add (add x y) z;
  addrC : forall x y, add x y = add y x;
  add0r : forall x, add zero x = x;
}.

HB.structure Definition AddComoid := { A of IsAddComoid A }.

Notation "0" := zero.
Infix "+" := add.

Check forall (M : AddComoid.type) (x : M), x + x = 0.
```

This is all we need to do in order to declare the `AddComoid` structure
and write statements in its signature.

We proceed by declaring how to obtain an Abelian group out of the
additive, commutative, monoid.

```coq
HB.mixin Record IsAbelianGrp A of IsAddComoid A := {
  opp : A -> A;
  addNr : forall x, opp x + x = 0;
}.

HB.structure Definition AbelianGrp := { A of IsAbelianGrp A & IsAddComoid A }.

Notation "- x" := (opp x).
```

Abelian groups feature the operations and properties given by the
`IsAbelianGrp` mixin (and its dependency `IsAddComoid`).

```coq
Lemma example (G : AbelianGrp.type) (x : G) : x + (- x) = - 0.
Proof. by rewrite addrC addNr -[LHS](addNr zero) addrC add0r. Qed.
```

We proceed by showing that `Z` is an example of both structures, and use
the lemma just proved on a statement about `Z`.

```coq
HB.instance Definition Z_CoMoid :=
  IsAddComoid.Build Z 0%Z Z.add Z.add_assoc Z.add_comm Z.add_0_l.
 
HB.instance Definition Z_AbGrp :=
  IsAbelianGrp.Build Z Z.opp Z.add_opp_diag_l.

Lemma example2 (x : Z) : x + (- x) = - 0.
Proof. by rewrite example. Qed.
```

## Documentation

This [paper](https://hal.inria.fr/hal-02478907) describes the language
in details, and the corresponding talk [is available on youtube](https://www.youtube.com/watch?v=F6iRaTlQrlo).
The [wiki](https://github.com/math-comp/hierarchy-builder/wiki) gathers some
tricks and FAQs.

### Installation & availability

<details><summary>(click to expand)</summary><p>

HB works on Coq 8.11, 8.12, 8.13 and 8.14

- You can install it via OPAM

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-hierarchy-builder
```

- You can use it in nix with the attribute `coqPackages_8_13.hierarchy-builder` e.g.
  via `nix-shell -p coq_8_13 -p coqPackages_8_13.hierarchy-builder`
 
</p></details>

### Key concepts

<details><summary>(click to expand)</summary><p>

- a *mixin* is a bare bone building block of the hierarchy, it packs operations
  and axioms.

- a *factory* is a package of operations and properties that is elaborated by
  HB to one or more mixin. A mixin is hence a trivial factory.

- a *structure* is declared by attaching zero or more factories to a type.

- a *builder* is a user provided piece of code capable of
  building one or more mixins from a factory.

- an *instance* is an example of a structure: it provides all operation and
  fulfills all axioms.

</p></details>

### The commands of HB

<details><summary>(click to expand)</summary><p>

- HB core commands:
  - `HB.mixin` declares a mixin,
  - `HB.structure` declares a structure,
  - `HB.factory` declares a factory,
  - `HB.builders` and `HB.end` declare a set of builders,
  - `HB.instance` declares a structure instance,
  - `HB.declare` declares a context with parameters, key and mixins.

- HB core tactic-in-term:
  - `HB.pack` to synthesize a structure instance in the middle of a term.

- HB utility commands:
  - `HB.export` exports a module and schedules it for re-export
  - `HB.reexport` exports all modules, instances and constants scheduled for
    re-export
  - `HB.lock` locks a definition behind an opaque symbol and an unfolding
    equation using Coq module system

- HB queries:
  - `HB.about` is similar to `About` but prints more info on HB structures, like
    the known instances and where they are declared
  - `HB.locate` is similar to `Locate`, prints file name and line of any global
    constant synthesized by HB
  - `HB.graph` prints the structure hierarchy to a dot file
  - `HB.howto` prints sequences of factories to equip a type with a given structure

- HB debug commands:
  - `HB.status` dumps the contents of the hierarchy (debug purposes)
  - `HB.check` is similar to `Check` (testing purposes)

The documentation of all commands can be found in the comments of
[structures.v](structures.v), search for `Elpi Command` and you will
find them. All commands can be prefixed with the attribute `#[verbose]`
to get an idea of what they are doing.

See also the `#[log]` attribute in the "Plan B" section below.

</p></details>

### Demos

<details><summary>(click to expand)</summary><p>

- [demo1](examples/demo1/) and [demo3](examples/demo3/) declare and evolve a hierarchy up to
  rings with various clients that are tested not to break when the hierarchy
  evolves
- [demo2](examples/demo2/) describes the subtle triangular interaction between groups,
  topological space and uniform spaces. Indeed, 1. all uniform spaces induce a
  topology, which makes them topological spaces, but 2. all topological groups
  (groups that are topological spaces such that the addition and opposite are
  continuous) induce a uniformity, which makes them uniform spaces. We solve
  this seamingly mutual dependency using HB.

</p></details>

### Plan B

Scared of making your project depend on HB? This section is for you.

HB is based on a thick layer of software which we plan to maintain, but we
also understand it can look scary. Hence this insurance plan. By passing
the attribute `#[log]` each command prints Coq commands which are equivalent to
its effect. By replacing each HB command by its equivalent Coq commands, you
can eliminate the dependency on HB from your project.

This is a "plan B", by looking at the output of`#[log]` you will realize that
HB commands are much nicer (and shorter) than the equivalent Coq code. The
point of a "plan B" is to avoid nightmares, not to be nicer than plan A ;-)

How can you be sure plan B works? We provide tools to check that in your CI, see
the details below.

<details><summary>(click to expand)</summary><p>


Hierarchy Builder commands can log their equivalent vernacular commands
to "patch" file (extension `.hb`). In order to do so, one has to
compile the project with the `COQ_ELPI_ATTRIBUTES` variable set. Eg

```shell
COQ_ELPI_ATTRIBUTES='hb(log(raw))' make
```

The `coq.hb` command line utility, provided by the `coq-hierarchy-builder` package,
is able to apply the generated patches: it comments out HB commands and
inserts their equivalent Coq commands.

```shell
coq.hb patch file1.v file2.v ...
```

The converse operation can be performed using the following command:

```shell
coq.hb reset file1.v file2.v ...
```

We recommend to setup a CI job testing plan B. If you are using
`docker-coq-action` the following snippet is a good start:

```yaml
  plan-B:
    runs-on: ubuntu-latest
    steps:
    - uses: actions/checkout@v2
    - uses: coq-community/docker-coq-action@v1
      with:
        opam_file: './your-project.opam'        # depends on coq-hierarchy-builder
        script: |
          # build the project so that it generates patch files
          COQ_ELPI_ATTRIBUTES="hb(log(raw))" make -j2
          # apply the patches
          coq.hb patch `find . -name \*.v`
          # check something happened
          if git diff --quiet; then echo "No patch!"; exit 1; fi
          # replace HB by a package with trivial dependencies, just to make
          # the From HB Require... line work
          opam remove coq-hierarchy-builder
          opam install coq-hierarchy-builder-shim
          # build the project without HB
          make -j2
```

</p></details>
