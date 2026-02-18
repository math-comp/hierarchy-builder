(* Accompanying material to Coq workshop presentation *)
From Coq Require Import ssreflect ssrfun ZArith.
From HB Require Import structures.

HB.mixin Record CMonoid_of_Type A := { (* The set of axioms making A a commutative monoid. *)
  zero  : A; add   : A -> A -> A;
  addrA : associative add;  (* `add` is associative  *)
  addrC : commutative add;  (* `add` is commutative  *)
  add0r : left_id zero add; (* `zero` is a neutral element *)
}.
HB.structure Definition CMonoid := { A of CMonoid_of_Type A }. (* The structure thereof. *)
Notation "0" := zero.
Infix    "+" := add.

(* The type of the operations and axioms depend on a CMonoid.type structure. *)
Check addrC. (* ?M : CMonoid.type |- commutative (@add ?M) *)

HB.mixin Record AbelianGrp_of_CMonoid A & CMonoid A := {
  opp   : A -> A;
  (* We can write `add` here since A is a  CMonoid   *)
  addNr : left_inverse zero opp add; (* `opp` is the additive inverse *)
}.
HB.structure Definition AbelianGrp := { A of AbelianGrp_of_CMonoid A }.
Notation "- x"   := (opp x).
Notation "x - y" := (add x (opp y)).

HB.mixin Record SemiRing_of_CMonoid A & CMonoid A := {
  one    : A;
  mul    : A -> A -> A;
  mulrA  : associative mul;  (* `mul` is associative   *)
  mul1r  : left_id one mul;  (* `one` is left neutral  *)
  mulr1  : right_id one mul; (* `one` is right neutral *)
  mulrDl : left_distributive mul add;  (* `mul` distributes over *)
  mulrDr : right_distributive mul add; (*   `add` on both sides  *)
  mul0r  : left_zero zero mul;  (* `zero` is absorbing `mul`     *)
  mulr0  : right_zero zero mul; (*   on both sides               *)
}.
HB.structure Definition SemiRing := { A of SemiRing_of_CMonoid A }.
Notation "1"  := one.
Infix    "*"  := mul.

(* We need no additional mixin to declare the Ring structure. *)
HB.structure Definition Ring := { A of SemiRing_of_CMonoid A & AbelianGrp_of_CMonoid A }.

(* An example statement in the signature of an Abelian group G, combining 0 and -. *)
Check forall G : AbelianGrp.type, forall x : G, x - x = 0.
(* An example statement in the signature of a Semiring S, combining 0, +, and *.  *)
Check forall S : SemiRing.type, forall x : S, x * 1 + 0 = x.
(* An example statement in the signature of a Ring R, combining -, 1 and *.  *)
Check forall R : Ring.type, forall x y : R, x * - (1 * y) = - x * y.

HB.instance Definition Z_CMonoid    := CMonoid_of_Type.Build Z 0%Z Z.add
  Z.add_assoc Z.add_comm Z.add_0_l.
HB.instance Definition Z_AbelianGrp := AbelianGrp_of_CMonoid.Build Z Z.opp Z.add_opp_diag_l.
HB.instance Definition Z_SemiRing   := SemiRing_of_CMonoid.Build Z 1%Z Z.mul
  Z.mul_assoc Z.mul_1_l Z.mul_1_r Z.mul_add_distr_r Z.mul_add_distr_l Z.mul_0_l Z.mul_0_r.

(* An example statement in the signature of the Z ring, combining Z, 0, +, -, 1 and * *)
Check forall x : Z, x * - (1 + x) = 0 + 1.
