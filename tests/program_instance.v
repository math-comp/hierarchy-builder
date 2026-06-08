From HB Require Import structures.
From Stdlib Require Import ZArith.

HB.mixin Record XX T := { X1 : T ; P : X1 = X1}.
HB.structure Definition x1  := { T of XX T }.



(* First, no props in the tactics *)
#[interactive] HB.instance Definition _ := XX.Build nat _ eq_refl.
exact 0. 
(* Elpi Trace Browser. *)
HB.end_instance.
(* Print HB_unnamed_factory_3. *)

(* then a prop *)
#[interactive] HB.instance Definition _ := XX.Build Type nat _.
reflexivity. 
HB.end_instance.
(* Print HB_unnamed_factory_14.  *)

(* then with a parameter *)
#[interactive] HB.instance Definition _ (xxxxx:nat) := XX.Build nat _ eq_refl.
exact (xxxxx+1).
HB.end_instance.
(* Print unnamed__25. *)

#[interactive] HB.instance Definition _ (n:Z) := XX.Build Z _ _.
exact (Z.add n 2%Z).
reflexivity.
HB.end_instance.
Inspect 5.
(* Print  HB_unnamed_factory_58.
Print  unnamed__57. *)
HB.instance Definition _ (n:bool) := XX.Build bool n eq_refl.



(* the rest *)
HB.mixin Record m1 T := { default1 : T }.
HB.structure Definition s1  := { T of m1 T }.

HB.mixin Record m2 T := { default2 : T ; default2b : T }.
(* HB.mixin Record m2 T := { default2 : T ; ax2 : exists t:T, t <> t }. *)
HB.structure Definition s2 := { T of m1 T & m2 T }.

HB.factory Record m3 T := { default3 : T }.

HB.builders Context T of m3 T.
HB.instance Definition _ := m1.Build T default3.

HB.instance Definition _ (n:nat) := m2.Build T default3 default3.
(* #[verbose,interactive] HB.instance Definition _ (n:nat) := m2.Build T _ _.
exact default3.
exact default3.
HB.end_instance. *)
HB.end.

(* TODO: this should work, but for now it breaks future declarations of instances *)
(* #[interactive] HB.instance Definition _ (n:Z) : m1 Z := m1.Build _ _.
destruct (Z.eqb n 0%Z).
- exact 4%Z.
- exact (Z.add n n).
HB.end_instance. 
Print HB_unnamed_factory_1710. *)

HB.mixin Record mt2 T := { d2 : T ; d2b : d2 = d2; d2bb : d2 = d2 }.
#[verbose,interactive] HB.instance Definition _ : mt2 nat := mt2.Build nat _ _ _.
exact 0.
reflexivity.
reflexivity.
HB.end_instance.
(* Print HB_unnamed_factory_12. *)
#[verbose,interactive] HB.instance Definition _ : m2 nat := m2.Build nat _ _.
exact 0.
exact 2.
HB.end_instance.


(* Fail #[interactive] HB.instance Definition _ : m1 Z := m1.Build Z 3%Z. *)


#[interactive] HB.instance Definition _ : m3 Z := m3.Build Z _.
exact 3%Z.
HB.end_instance.
HB.about Z.




(* HB.about nat. *)





(* FACTORY STUFF *)

HB.mixin Record isSemiGroup T := {
    op : T -> T -> T;
    opA : forall x y z, op x (op y z) = op (op x y) z
  }.    
HB.structure Definition SemiGroup := {T of isSemiGroup T}.

HB.mixin Record semiGroup_isGroup T of isSemiGroup T := {
    e : T;
    idl : forall x, op e x = x;
    idr : forall x, op x e = x;
    invl : forall x, exists xinv, op x xinv = e;
    invr : forall x, exists xinv, op xinv x = e;
}.
HB.structure Definition Group := {T of isSemiGroup T & semiGroup_isGroup T}.


(* Factory: New definition of group *)
HB.factory Record isGroup T := {
    op : T -> T -> T;
    opA' : forall x y z, op (op x y) z = op x (op y z);
    e : T;
    idl' : forall x, op e x = x;
    idr : forall x, op x e = x;
    invl : forall x, exists xinv, op x xinv = e;
    invr : forall x, exists xinv, op xinv x = e;
    default : T
}.


HB.about isGroup.

HB.builders Context T of isGroup T.
#[verbose,interactive] HB.instance Definition _ := isSemiGroup.Build T _ _.
exact op. (*why is the goal not even shelved?*)
simpl. intros.
rewrite opA'. 
reflexivity.
HB.end_instance.
(* Print unnamed. *)

HB.instance Definition _ := semiGroup_isGroup.Build T e idl' idr invl invr.
HB.end.

HB.about isGroup.

Fail HB.structure Definition Group2 := {T of isGroup T &}.

Lemma left_id (T : Group.type) (x y : T) : op e x = x.
  Proof. apply idl. Qed.


HB.instance  Definition _ := isSemiGroup.Build Z Z.add Z.add_assoc.

HB.instance Definition _ := isSemiGroup.Build Z Z.add Z.add_assoc.
HB.about Z.

Lemma Zaddel :  forall x:Z, exists xinv:Z, Z.add x xinv = 0%Z.
  Proof. intros. exists (Z.opp x). apply Z.add_opp_diag_r. Qed.
Lemma Zadder :  forall x:Z, exists xinv:Z, Z.add xinv x = 0%Z.
  Proof. intros. exists (Z.opp x). apply Z.add_opp_diag_l. Qed.
HB.instance Definition _ := semiGroup_isGroup.Build Z 0%Z Z.add_0_l Z.add_0_r Zaddel Zadder.
HB.about Z.
