[![Build Status](https://travis-ci.org/math-comp/hierarchy-builder.svg?branch=master)](https://travis-ci.org/math-comp/hierarchy-builder)

# Hierarchy Builder

High level commands to declare and evolve a hierarchy based on packed classes.

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
HB.structure Definition AddComoid := { A of AddComoid_of_Type.axioms A }.

Notation "0" := zero.
Infix "+" := add.

Check forall (M : AddComoid.type) (x : M), x + x = 0.
```

This is all we need to do in order to declare the `AddComoid` structure
and write statements in its signature.

We proceed by declaring how to obtain an Abelian group out of the
additive, commutative, monoid.

```coq
HB.mixin Record AbelianGrp_of_AddComoid A of AddComoid.axioms A := {
  opp : A -> A;
  addNr : forall x, opp x + x = 0;
}.
HB.structure Definition AbelianGrp := { A of AbelianGrp_of_AddComoid.axioms A & }.

Notation "- x" := (opp x).
```

Abelian groups feature the operations and properties given by the
`AbelianGrp_of_AddComoid.axioms` and `AddComoid_of_Type.axioms` mixins.

```coq
Lemma example (G : AbelianGrp.type) (x : G) : x + (- x) = - 0.
Proof. by rewrite addrC addNr -[LHS](addNr zero) addrC add0r. Qed.
```

We proceed by showing that `Z` is an example of both structures, and use
the lemma just proved on a statement about `Z`.

```coq
Definition Z_CoMoid := AddComoid_of_Type.Axioms Z 0%Z Z.add Z.add_assoc Z.add_comm Z.add_0_l.
HB.instance Z Z_CoMoid.
Definition Z_AbGrp := AbelianGrp_of_AddComoid.Axioms Z Z.opp Z.add_opp_diag_l.
HB.instance Z Z_AbGrp.

Lemma example2 (x : Z) : x + (- x) = - 0.
Proof. by rewrite example. Qed.
```

## Documentation

#### Installation & availability

HB works on Coq 8.10 and 8.11. you can install it via OPAM

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-hierarchy-builder
```

#### Key concepts

- a *mixin* is a bare bone building block of the hierarchy, it packs operations
  and axioms.

- a *factory* is a package of operations and properties that is elaborated by
  HB to one or more mixin. A mixin is hence a trivial factory.

- a *structure* is declared by attaching zero or more factories to a type.

- a *builder* is user provided piece of code capable of
  building one or more mixins from a factory.

- an *instance* is an example of a structure: it provides all operation and
  fulfills all axioms.

A [draft paper](https://hal.inria.fr/hal-02478907) describes the language in
more detail.

#### The commands provided by hb

- `HB.mixin` declares a mixin
- `HB.structure` declares a structure
- `HB.factory` declares a factory
- `HB.builders` and `HB.end` declares a set of builders
- `HB.instance` declares a structure instance
- `HB.status` dumps the contents of the hierarchy (debug purposes)

Their documentation can be found in the comments of [structures.v](structures.v),
search for `Elpi Command` and you will find them. All commands can be
prefixed with the attribute `#[verbose]`.

#### Demos

- [demo1](demo1/) and [demo3](demo3/) declare and evolve a hierarchy up to
  rings with various clients that are tested not to break when the hierarchy
  evolves
- [demo2](demo2/) TODO: explain the tricky thing
