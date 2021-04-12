From HB Require Import structures.

HB.lock Definition foo := 3.

Definition nat1 := nat.

HB.lock Definition bar : nat1 := 3.

HB.lock Definition baz n : nat := 3 + n.

Axiom bigbody : Type -> Type -> Type.
Axiom bigop : forall R I : Type, R -> list I -> (I -> bigbody R I) -> R.

HB.lock Definition xxx := bigop.

