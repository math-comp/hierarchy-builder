From HB Require Import structures.
From Coq Require Import ssreflect ZArith.

#[verbose]
HB.mixin Record AddComoid_of_Type A := {
  zero : A;
  add : A -> A -> A;
  addrA : forall x y z, add x (add y z) = add (add x y) z;
  addrC : forall x y, add x y = add y x;
  add0r : forall x, add zero x = x;
}.
#[verbose]
HB.structure Definition AddComoid := { A of AddComoid_of_Type A }.

Notation "0" := zero.
Infix "+" := add.

Check forall (M : AddComoid.type) (x : M), x + x = 0.

#[verbose]
HB.mixin Record AbelianGrp_of_AddComoid A of AddComoid A := {
  opp : A -> A;
  addNr : forall x, opp x + x = 0;
}.
#[verbose]
HB.structure Definition AbelianGrp := { A of AbelianGrp_of_AddComoid A & }.

Notation "- x" := (opp x).

Lemma example (G : AbelianGrp.type) (x : G) : x + (- x) = - 0.
Proof. by rewrite addrC addNr -[LHS](addNr zero) addrC add0r. Qed.

Definition Z_CoMoid := AddComoid_of_Type.Build Z 0%Z Z.add Z.add_assoc Z.add_comm Z.add_0_l.
HB.instance Z Z_CoMoid.
Definition Z_AbGrp := AbelianGrp_of_AddComoid.Build Z Z.opp Z.add_opp_diag_l.
HB.instance Z Z_AbGrp.

Lemma example2 (x : Z) : x + (- x) = - 0.
Proof. by rewrite example. Qed.
