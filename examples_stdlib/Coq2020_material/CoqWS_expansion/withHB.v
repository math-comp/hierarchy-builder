(* Accompanying material to Coq workshop presentation *)
From Coq Require Import ssreflect ssrfun ZArith.
From HB Require Import structures.
Set Warnings "-redundant-canonical-projection".

HB.mixin
  Record CMonoid_of_Type A := {
    zero  : A;
    add   : A -> A -> A;
    addrA : associative add;
    addrC : commutative add;
    add0r : left_id zero add;
  }.

HB.structure
  Definition CMonoid := { A of CMonoid_of_Type A }.

HB.mixin
  Record AbelianGrp_of_CMonoid A & CMonoid A := {
    opp   : A -> A;
    addNr : left_inverse zero opp add;
  }.

HB.structure
  Definition AbelianGrp := { A of AbelianGrp_of_CMonoid A & }.
