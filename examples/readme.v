From HB Require Import structures.
From Corelib Require Import ssreflect BinNums IntDef.
Set Printing Universes.
Set Universe Polymorphism.
Unset Printing Records.

#[verbose]
HB.mixin Record AddComoid_of_Type (A : Type) := {
  zero : A;
  add : A -> A -> A;
  addrA : forall x y z, add x (add y z) = add (add x y) z;
  addrC : forall x y, add x y = add y x;
  add0r : forall x, add zero x = x;
}.
HB.structure Definition AddComoid := { A of AddComoid_of_Type A }.

Notation "0" := zero.
Infix "+" := add.

About AddComoid_of_Type.axioms_.

Check forall (M : AddComoid.type) (x : M), x + x = 0.

HB.mixin Record AbelianGrp_of_AddComoid A of AddComoid_of_Type A := {
  opp : A -> A;
  addNr : forall x, opp x + x = 0;
}.
HB.structure Definition AbelianGrp := { A of AbelianGrp_of_AddComoid A & }.

Notation "- x" := (opp x).

Lemma example (G : AbelianGrp.type) (x : G) : x + (- x) = - 0.
Proof. by rewrite addrC addNr -[LHS](addNr zero) addrC add0r. Qed.

Axiom Z_add_assoc : forall x y z, Z.add x (Z.add y z) = Z.add (Z.add x y) z.
Axiom Z_add_comm : forall x y, Z.add x y = Z.add y x.
Axiom Z_add_0_l : forall x, Z.add Z0 x = x.
Axiom Z_add_opp_diag_l : forall x, Z.add (Z.opp x) x = Z0.

HB.instance Definition Z_CoMoid := AddComoid_of_Type.Build Z Z0 Z.add Z_add_assoc Z_add_comm Z_add_0_l.
HB.instance Definition Z_AbGrp := AbelianGrp_of_AddComoid.Build Z Z.opp Z_add_opp_diag_l.

Lemma example2 (x : Z) : x + (- x) = - 0.
Proof. by rewrite example. Qed.

Check AbelianGrp.on Z.

HB.graph "readme.dot".
HB.about Z.

Section Test.
HB.declare Context (T : Type) (p : AddComoid_of_Type T) (q : AbelianGrp_of_AddComoid T).

Goal forall x : T, x + -x = 0.
Abort.

End Test.
