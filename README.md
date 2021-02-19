<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Hierarchy Builder

[![Docker CI][docker-action-shield]][docker-action-link]
[![Nix CI][nix-action-shield]][nix-action-link]
[![Chat][chat-shield]][chat-link]

[docker-action-shield]: https://github.com/math-comp/hierarchy-builder/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/math-comp/hierarchy-builder/actions?query=workflow:"Docker%20CI"

[nix-action-shield]: https://github.com/math-comp/hierarchy-builder/workflows/Nix%20CI/badge.svg?branch=master
[nix-action-link]: https://github.com/math-comp/hierarchy-builder/actions?query=workflow:"Nix%20CI"
[chat-shield]: https://img.shields.io/badge/zulip-join_chat-brightgreen.svg
[chat-link]: https://coq.zulipchat.com/#narrow/stream/237868-Hierarchy-Builder




Hierarchy Builder is a high level language to build hierarchies of
algebraic structures and make these hierarchies evolve without breaking
user code. The key concepts are the ones of factory, builder and
abbreviation that let the hierarchy developer describe an actual
interface for their library. Behind that interface the developer can
provide appropriate code to ensure retro compatibility.

## Meta

- Author(s):
  - Cyril Cohen (initial)
  - Kazuhiko Sakaguchi (initial)
  - Enrico Tassi (initial)
- License: [MIT](LICENSE)
- Compatible Coq versions: Coq 8.11 to 8.13 (or dev)
- Additional dependencies:
  - [Coq elpi](https://github.com/LPCIC/coq-elpi)
- Coq namespace: `HB`
- Related publication(s):
  - [Hierarchy Builder: algebraic hierarchies made easy in Coq with Elpi](https://hal.inria.fr/hal-02478907) doi:[10.4230/LIPIcs.FSCD.2020.34](https://doi.org/10.4230/LIPIcs.FSCD.2020.34)
  - [Hierarchy Builder: FSCD Talk](https://www.youtube.com/watch?v=F6iRaTlQrlo)) 

## Building and installation instructions

### Opam installation

<details><summary>(click to expand)</summary><p>

The easiest way to install the latest released version of Hierarchy Builder
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-hierarchy-builder
```

</p></details>

### Manual installation

<details><summary>(click to expand)</summary><p>

To instead build and install manually, do:

``` shell
git clone https://github.com/math-comp/hierarchy-builder.git
cd hierarchy-builder
make   # or make -j <number-of-cores-on-your-machine> 
make install VFILES=structures.v
```

</p></details>


## Example

```coq
From HB Require Import structures.
From Coq Require Import ssreflect ZArith.

HB.mixin Record AddComoid_of_Type A := {
  zero : A;
  add : A -> A -> A;
  addrA : forall x y z, add x (add y z) = add (add x y) z;
  addrC : forall x y, add x y = add y x;
  add0r : forall x, add zero x = x;
}.
HB.structure Definition AddComoid := { A of AddComoid_of_Type A }.

Notation "0" := zero.
Infix "+" := add.

Check forall (M : AddComoid.type) (x : M), x + x = 0.
```

This is all we need to do in order to declare the `AddComoid` structure
and write statements in its signature.

We proceed by declaring how to obtain an Abelian group out of the
additive, commutative, monoid.

```coq
HB.mixin Record AbelianGrp_of_AddComoid A of AddComoid A := {
  opp : A -> A;
  addNr : forall x, opp x + x = 0;
}.
HB.structure Definition AbelianGrp := { A of AbelianGrp_of_AddComoid A & }.

Notation "- x" := (opp x).
```

Abelian groups feature the operations and properties given by the
`AbelianGrp_of_AddComoid` mixin (and its dependency `AddComoid`).

```coq
Lemma example (G : AbelianGrp.type) (x : G) : x + (- x) = - 0.
Proof. by rewrite addrC addNr -[LHS](addNr zero) addrC add0r. Qed.
```

We proceed by showing that `Z` is an example of both structures, and use
the lemma just proved on a statement about `Z`.

```coq
HB.instance Definition Z_CoMoid := AddComoid_of_Type.Build Z 0%Z Z.add Z.add_assoc Z.add_comm Z.add_0_l.
HB.instance Definition Z_AbGrp := AbelianGrp_of_AddComoid.Build Z Z.opp Z.add_opp_diag_l.

Lemma example2 (x : Z) : x + (- x) = - 0.
Proof. by rewrite example. Qed.
```

## Documentation

#### Status

The software is beta-quality, it works but error messages should be improved.

The current version forces the carrier to be a type, ruling hierarchies of morphisms out.

This [draft paper](https://hal.inria.fr/hal-02478907) describes the language
in full detail.

#### Alternative Installation instructions

<details><summary>(click to expand)</summary><p>

- You can use it in nix with the attribute `coqPackages_8_13.hierarchy-builder` e.g. via `nix-shell -p coq_8_13 -p coqPackages_8_13.hierarchy-builder`

</p></details>

#### Key concepts

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

#### The commands of HB

<details><summary>(click to expand)</summary><p>

- `HB.mixin` declares a mixin
- `HB.structure` declares a structure
- `HB.factory` declares a factory
- `HB.builders` and `HB.end` declares a set of builders
- `HB.instance` declares a structure instance
- `HB.status` dumps the contents of the hierarchy (debug purposes)

Their documentation can be found in the comments of [structures.v](structures.v),
search for `Elpi Command` and you will find them. All commands can be
prefixed with the attribute `#[verbose]` to get an idea of what they are doing.

</p></details>

#### Demos

<details><summary>(click to expand)</summary><p>

- [demo1](demo1/) and [demo3](demo3/) declare and evolve a hierarchy up to
  rings with various clients that are tested not to break when the hierarchy
  evolves
- [demo2](demo2/) describes the subtle triangular interaction between groups,
  topological space and uniform spaces. Indeed, 1. all uniform spaces induce a
  topology, which makes them topological spaces, but 2. all topological groups
  (groups that are topological spaces such that the addition and opposite are
  continuous) induce a uniformity, which makes them uniform spaces. We solve
  this seamingly mutual dependency using HB.

</p></details>
