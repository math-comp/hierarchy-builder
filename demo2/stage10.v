From Coq Require Import ssreflect ssrfun ssrbool ZArith QArith.
From HB Require Import structures.
From HB.demo2 Require Import classical.

Declare Scope hb_scope.
Delimit Scope hb_scope with G.

Local Open Scope classical_set_scope.
Local Open Scope hb_scope.

Module Stage10.

HB.structure Definition TYPE := { A of True }.

HB.mixin Record AddAG_of_TYPE A := {
  zero : A;
  add : A -> A -> A;
  opp : A -> A;
  addrA : associative add;
  addrC : commutative add;
  add0r : left_id zero add;
  addNr : left_inverse zero opp add;
}.
HB.structure Definition AddAG := { A of AddAG_of_TYPE A }.

Notation "0" := zero : hb_scope.
Infix "+" := (@add _) : hb_scope.
Notation "- x" := (@opp _ x) : hb_scope.
Notation "x - y" := (x + - y) : hb_scope.

(* Theory *)

Section AddAGTheory.
Variable A : AddAG.type.
Implicit Type (x : A).

Lemma addr0 : right_id (@zero A) add.
Proof. by move=> x; rewrite addrC add0r. Qed.

Lemma addrN : right_inverse (@zero A) opp add.
Proof. by move=> x; rewrite addrC addNr. Qed.

Lemma subrr x : x - x = 0.
Proof. by rewrite addrN. Qed.

Lemma addrK : right_loop (@opp A) (@add A).
Proof. by move=> x y; rewrite -addrA subrr addr0. Qed.

Lemma addKr : left_loop (@opp A) (@add A).
Proof. by move=> x y; rewrite addrA addNr add0r. Qed.

Lemma addrNK : rev_right_loop (@opp A) (@add A).
Proof. by move=> y x; rewrite -addrA addNr addr0. Qed.

Lemma addNKr : rev_left_loop (@opp A) (@add A).
Proof. by move=> x y; rewrite addrA subrr add0r. Qed.

Lemma addrAC : right_commutative (@add A).
Proof. by move=> x y z; rewrite -!addrA [y + z]addrC. Qed.

Lemma addrCA : left_commutative (@add A).
Proof. by move=> x y z; rewrite !addrA [x + y]addrC. Qed.

Lemma addrACA : interchange (@add A) add.
Proof. by move=> x y z t; rewrite !addrA [x + y + z]addrAC. Qed.

Lemma opprK : involutive (@opp A).
Proof. by move=> x; apply: (can_inj (addrK (- x))); rewrite addNr addrN. Qed.

Lemma opprD x y : - (x + y) = - x - y.
Proof.
apply: (can_inj (addKr (x + y))).
by rewrite subrr addrACA !subrr addr0.
Qed.

Lemma opprB x y : - (x - y) = y - x.
Proof. by rewrite opprD opprK addrC. Qed.

End AddAGTheory.

HB.mixin Record Ring_of_AddAG A of AddAG A := {
  one : A;
  mul : A -> A -> A;
  mulrA : associative mul;
  mulr1 : left_id one mul;
  mul1r : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
}.
HB.factory Record Ring_of_TYPE A := {
  zero : A;
  one : A;
  add : A -> A -> A;
  opp : A -> A;
  mul : A -> A -> A;
  addrA : associative add;
  addrC : commutative add;
  add0r : left_id zero add;
  addNr : left_inverse zero opp add;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
}.

HB.builders Context A (a : Ring_of_TYPE A).

Definition to_AddAG_of_TYPE := AddAG_of_TYPE.Build A
    _ _ _ addrA addrC add0r addNr.
  HB.instance A to_AddAG_of_TYPE.
  Definition to_Ring_of_AddAG :=
    Ring_of_AddAG.Build _ _ _ mulrA mul1r
      mulr1 mulrDl mulrDr.
  HB.instance A to_Ring_of_AddAG.
HB.end.

HB.structure Definition Ring := { A of Ring_of_TYPE A }.

Notation "1" := one : hb_scope.
Infix "*" := (@mul _) : hb_scope.

HB.mixin Record Topological T := {
  open : (T -> Prop) -> Prop;
  open_setT : open setT;
  open_bigcup : forall {I} (D : set I) (F : I -> set T),
    (forall i, D i -> open (F i)) -> open (\bigcup_(i in D) F i);
  open_setI : forall X Y : set T, open X -> open Y -> open (setI X Y);
}.
HB.structure Definition TopologicalSpace := { A of Topological A }.

Hint Extern 0 (open setT) => now apply: open_setT : core.

HB.factory Record TopologicalBase T := {
  open_base : set (set T);
  open_base_covers : setT `<=` \bigcup_(X in open_base) X;
  open_base_cup : forall X Y : set T, open_base X -> open_base Y ->
    forall z, (X `&` Y) z -> exists2 Z, open_base Z & Z z /\ Z `<=` X `&` Y
}.

HB.builders Context T (a : TopologicalBase T).

  Definition open_of : (T -> Prop) -> Prop :=
    [set A | exists2 D, D `<=` open_base & A = \bigcup_(X in D) X].

  Lemma open_of_setT : open_of setT.  Proof.
  exists open_base; rewrite // predeqE => x; split=> // _.
  by apply: open_base_covers.
  Qed.

  Lemma open_of_bigcup {I} (D : set I) (F : I -> set T) :
    (forall i, D i -> open_of (F i)) -> open_of (\bigcup_(i in D) F i).
  Proof. Admitted.

  Lemma open_of_cap X Y : open_of X -> open_of Y -> open_of (X `&` Y).
  Proof. Admitted.

  Definition to_Topological :=
    Topological.Build T _ open_of_setT (@open_of_bigcup) open_of_cap.
  HB.instance T to_Topological.

HB.end.

Section ProductTopology.
  Variables (T1 T2 : TopologicalSpace.type).

  Definition prod_open_base :=
    [set A | exists (A1 : set T1) (A2 : set T2),
      open A1 /\ open A2 /\ A = setM A1 A2].

  Lemma prod_open_base_covers : setT `<=` \bigcup_(X in prod_open_base) X.
  Proof.
  move=> X _; exists setT => //; exists setT, setT; do ?split.
  - exact: open_setT.
  - exact: open_setT.
  - by rewrite predeqE.
  Qed.

  Lemma prod_open_base_setU X Y :
    prod_open_base X -> prod_open_base Y ->
      forall z, (X `&` Y) z ->
        exists2 Z, prod_open_base Z & Z z /\ Z `<=` X `&` Y.
  Proof.
  move=> [A1 [A2 [A1open [A2open ->]]]] [B1 [B2 [B1open [B2open ->]]]].
  move=> [z1 z2] [[/=Az1 Az2] [/= Bz1 Bz2]].
  exists ((A1 `&` B1) `*` (A2 `&` B2)).
    by eexists _, _; do ?[split; last first]; apply: open_setI.
  by split => // [[x1 x2] [[/=Ax1 Bx1] [/=Ax2 Bx2]]].
  Qed.

  Definition prod_topology :=
    TopologicalBase.Build (TopologicalSpace.sort T1 * TopologicalSpace.sort T2)%type _ prod_open_base_covers prod_open_base_setU.
  HB.instance ((TopologicalSpace.sort T1 * TopologicalSpace.sort T2)%type) prod_topology.

End ProductTopology.

Definition continuous {T T' : TopologicalSpace.type} (f : T -> T') :=
  forall B : set T', open B -> open (f@^-1` B).

Definition continuous2 {T T' T'': TopologicalSpace.type}
  (f : T -> T' -> T'') := continuous (fun xy => f xy.1 xy.2).

HB.mixin Record JoinTAddAG T of AddAG_of_TYPE T & Topological T := {
  add_continuous : continuous2 (add : T -> T -> T);
  opp_continuous : continuous (opp : T -> T)
}.

HB.structure Definition TAddAG := { A of Topological A & AddAG_of_TYPE A & JoinTAddAG A }.

(* Instance *)

Definition Z_ring_axioms :=
  Ring_of_TYPE.Build Z 0%Z 1%Z Z.add Z.opp Z.mul
    Z.add_assoc Z.add_comm Z.add_0_l Z.add_opp_diag_l
    Z.mul_assoc Z.mul_1_l Z.mul_1_r
    Z.mul_add_distr_r Z.mul_add_distr_l.
HB.instance Z Z_ring_axioms.

Example test1 (m n : Z) : (m + n) - n + 0 = m.
Proof. by rewrite addrK addr0. Qed.

Require Import Qcanon.
Search _ Qc "plus" "opp".

Lemma Qcplus_opp_l q : - q + q = 0.
Proof. by rewrite Qcplus_comm Qcplus_opp_r. Qed.

Definition Qc_ring_axioms :=
  Ring_of_TYPE.Build Qc 0%Qc 1%Qc Qcplus Qcopp Qcmult
    Qcplus_assoc Qcplus_comm Qcplus_0_l Qcplus_opp_l
    Qcmult_assoc Qcmult_1_l Qcmult_1_r
    Qcmult_plus_distr_l Qcmult_plus_distr_r.
HB.instance Qc Qc_ring_axioms.

Obligation Tactic := idtac.
Definition Qcopen_base : set (set Qc) :=
  [set A | exists a b : Qc, forall z, A z <-> a < z /\ z < b].
Program Definition QcTopological := TopologicalBase.Build Qc Qcopen_base _ _.
Next Obligation.
move=> x _; exists [set y | x - 1 < y < x + 1].
  by exists (x - 1), (x + 1).
split; rewrite Qclt_minus_iff.
  by rewrite -[_ + _]/(x - (x - 1))%G opprB addrCA subrr.
by rewrite -[_ + _]/(x + 1 - x)%G addrAC subrr.
Qed.
Next Obligation.
move=> X Y [aX [bX Xeq]] [aY [bY Yeq]] z [/Xeq [aXz zbX] /Yeq [aYz zbY]].
Admitted.
HB.instance Qc QcTopological.

Program Definition QcJoinTAddAG := JoinTAddAG.Build Qc _ _.
Next Obligation. Admitted.
Next Obligation. Admitted.
HB.instance Qc QcJoinTAddAG.

End Stage10.