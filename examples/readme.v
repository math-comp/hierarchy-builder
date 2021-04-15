From HB Require Import structures.
From Coq Require Import ssreflect ZArith.

#[verbose, log]
HB.mixin Record AddComoid_of_Type A := {
  zero : A;
  add : A -> A -> A;
  addrA : forall x y z, add x (add y z) = add (add x y) z;
  addrC : forall x y, add x y = add y x;
  add0r : forall x, add zero x = x;
}.
#[verbose, log(raw)]
HB.structure Definition AddComoid := { A of AddComoid_of_Type A }.

Notation "0" := zero.
Infix "+" := add.

Check forall (M : AddComoid.type) (x : M), x + x = 0.

HB.mixin Record AbelianGrp_of_AddComoid A of AddComoid_of_Type A := {
  opp : A -> A;
  addNr : forall x, opp x + x = 0;
}.
HB.structure Definition AbelianGrp := { A of AbelianGrp_of_AddComoid A & }.

Notation "- x" := (opp x).

Lemma example (G : AbelianGrp.type) (x : G) : x + (- x) = - 0.
Proof. by rewrite addrC addNr -[LHS](addNr zero) addrC add0r. Qed.

HB.instance Definition Z_CoMoid := AddComoid_of_Type.Build Z 0%Z Z.add Z.add_assoc Z.add_comm Z.add_0_l.
HB.instance Definition Z_AbGrp := AbelianGrp_of_AddComoid.Build Z Z.opp Z.add_opp_diag_l.

Lemma example2 (x : Z) : x + (- x) = - 0.
Proof. by rewrite example. Qed.

Check AbelianGrp.on Z.

HB.graph "readme.dot".
