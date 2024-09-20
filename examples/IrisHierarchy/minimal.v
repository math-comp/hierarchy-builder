From Coq Require Import ssreflect ssrfun.
From HB Require Import structures.
From Coq Require Import List Relations Morphisms.

HB.mixin Record isSetoid A := {
  equiv : relation A;
  equivP : Equivalence equiv
}.
#[short(type="setoid")]
HB.structure Definition Setoid := {A of isSetoid A}.
#[global] Existing Instance equivP.

HB.mixin Record isFoo A := {}.
HB.structure Definition Foo := {A of isFoo A }.

HB.mixin Record isPU A := {}.
HB.structure Definition PU := {A of isFoo A & isSetoid A & isPU A}.

Lemma not_breaking (A : setoid) : Equivalence (@equiv A).
Proof. apply equivP. Qed.

Lemma breaking (A : PU.type) : Equivalence (@equiv A).
Proof. apply equivP.



#[global]
Instance equiv_Proper (A : setoid) :
   Proper (@equiv A ==> equiv ==> iff) equiv.
Admitted.

(* Module setoid_list. *)
#[local]
Instance Forall2_equivalence A (R : relation A)
  of Equivalence R : Equivalence (Forall2 R).
Proof.
Admitted.

HB.instance Definition test (A : setoid) :=
  isSetoid.Build (list A) (Forall2 (@equiv A)) _.
(* End setoid_list. *)
(* HB.instance Definition _ A := setoid_list.test A. *)

#[global]
Lemma cons_Proper (A : setoid) :
   Proper (equiv ==> equiv ==> equiv) (@cons A).
Proof. by constructor. Qed.
#[global]
Hint Extern 0 (Proper _ cons) =>
  apply: cons_Proper   : typeclass_instances.

Lemma foo (A : setoid) (x y : A) :
  equiv x y -> equiv (x :: y :: nil) (y :: x :: nil).
Proof. move->. reflexivity. Qed.

Definition trivialSetoid T := isSetoid.Build T eq eq_equivalence.

Definition discrete T : Type := T.
HB.instance Definition _ T := trivialSetoid (discrete T).

HB.instance Definition _ := Setoid.copy nat (discrete nat).

Lemma foo' (x y : list (list nat)) :
  equiv x y -> equiv (x :: y :: nil) (y :: x :: nil).
Proof. move->. reflexivity. Qed.

HB.mixin Record RawSetoid_isRawOfe A of RawSetoid A := {
  dist : nat -> relation A;
}.
#[short(type="rawofe")]
HB.structure Definition RawOfe :=
  { A of RawSetoid A & RawSetoid_isRawOfe A}.

(* TODO: improve error message when removing explicit A *)
HB.mixin Record Setoid_Raw_isOfe A of
    Setoid A & RawSetoid_isRawOfe A := {
  distP : forall n, Equivalence (@dist A n);
  equiv_dist : forall x y : A,
    equiv x y <-> (forall n, dist n x y);
  dist_S : forall n (x y : A), dist (S n) x y -> dist n x y
}.

HB.factory Record Setoid_isOfe A of Setoid A := {
  dist : nat -> relation A;
  distP : forall n, Equivalence (dist n);
  equiv_dist : forall x y,
    equiv x y <-> (forall n, dist n x y);
  dist_S : forall n x y, dist (S n) x y -> dist n x y
}.
HB.builders Context A of Setoid_isOfe A.
  HB.instance Definition _ := RawSetoid_isRawOfe.Build A dist.
  HB.instance Definition _ :=
    Setoid_Raw_isOfe.Build A distP equiv_dist dist_S.
HB.end.

#[short(type="ofe")]
HB.structure Definition Ofe := {A of Setoid_isOfe A & Setoid A}.

HB.factory Record isOfe A := {
  dist : nat -> relation A;
  distP : forall n, Equivalence (dist n);
  dist_S : forall n x y, dist (S n) x y -> dist n x y
}.
HB.builders Context A of isOfe A.
  Definition equiv x y := forall n, dist n x y.
  Lemma equivP : Equivalence equiv.
  Proof. Admitted.
  HB.instance Definition _ := isSetoid.Build A equiv equivP.
  (* TODO: this should emit a warning! *)
  HB.instance Definition _ := isSetoid.Build A equiv equivP.
  HB.instance Definition _ := Setoid_isOfe.Build A dist distP
    (fun _ _ => iff_refl _) dist_S.

  Definition equiv' x y := forall n, dist (S n) x y.
  Lemma equiv'P : Equivalence equiv'.
  Proof. Admitted.
  (* TODO: this should error now! *)
  HB.instance Definition _ := isSetoid.Build A equiv' equiv'P.
HB.end.

HB.factory Record Setoid_isTrivialOfe A of Setoid A := {}.
HB.builders Context A of Setoid_isTrivialOfe A.
  Lemma equiv_dist :
    forall x y : A, equiv x y <-> (forall _ : nat, equiv x y).
  Proof. by move=> x y; split => //; apply; exact: 0. Qed.
  HB.instance Definition _ : Setoid_isOfe A :=
    Setoid_isOfe.Build A (fun _ => equiv) (fun _ => equivP)
                        equiv_dist (fun _ _ _ => id).
HB.end.

HB.instance Definition _ T := Setoid_isTrivialOfe.Build (discrete T).

HB.instance Definition _ := Ofe.copy nat (discrete nat).

#[global] Existing Instance distP.

#[global]
Instance dist_Proper (A : ofe) n :
   Proper (@dist A n ==> dist n ==> iff) (dist n).
Admitted.

#[global]
Instance dist_equiv_Proper (A : ofe) n :
   Proper (@equiv A ==> equiv ==> iff) (dist n).
Admitted.

Section ofe_ist.
Variable (A : ofe).

HB.instance Definition _ :=
  RawSetoid_isRawOfe.Build (list A)
   (fun n => Forall2 (@dist A n)).

(* TODO: Fix printing *)
Lemma list_isOfe : Setoid_Raw_isOfe (list A).
Proof.
constructor.
Admitted.

HB.instance Definition _ := list_isOfe.
End ofe_ist.

#[global]
Instance cons_ofe_Proper (A : ofe) n :
   Proper (dist n ==> dist n ==> dist n) (@cons A).
Proof. by constructor. Qed.

Global Instance : Params (@cons) 1 := {}.
Global Instance : Params (@dist) 2 := {}.
Global Instance : Params (@equiv) 1 := {}.

Lemma breaking (A : setoid) : Equivalence (@equiv A).
Proof. apply equivP. Qed.

Lemma breaking' (A : ofe) : Equivalence (@equiv A).
Proof. Fail apply equivP. exact: equivP. Qed.

Lemma foo'' (A : ofe) (x y : A) :
  equiv x y -> dist 2 (x :: y :: nil) (y :: x :: nil).
Proof.

move=> exy.
Set Printing All.
Set Typeclasses Debug.

Fail rewrite exy.
assert (@Equivalence _ (@equiv A)).
  apply: equivP.


assert
(@Equivalence (Ofe.sort A)
          (@equiv (iris_Setoid__to__iris_RawSetoid
      (iris_Ofe__to__iris_Setoid A)))).
  apply: equivP.
  eauto with typeclass_instances.

assert (exists r0 r,
(@Proper
   (forall (_ : Ofe.sort A)
           (_ : list (Ofe.sort A)), list (Ofe.sort A))
   (@respectful (Ofe.sort A)
      (forall _ : list (Ofe.sort A), list (Ofe.sort A))
      (@equiv (iris_Ofe__to__iris_RawSetoid A))
      (@respectful (list (Ofe.sort A))
         (list (Ofe.sort A)) r0 r))
   (@cons (Ofe.sort A)))).
eexists _, _.
  eauto with typeclass_instances.

  eapply cons_Proper.
  eauto with typeclass_instances.

Fail rewrite -> exy.

eapply dist_equiv_Proper.
eapply cons_Proper.
  exact exy.
reflexivity.
eapply cons_Proper.
  reflexivity.
eapply cons_Proper.
  exact exy.
  reflexivity.

eapply equiv_Proper.

apply/dist_equiv_Proper.
apply: (dist_equiv_Proper _ _ _ _ _ _ _ _).2.
rewrite -> exy.
move->.

 move->. reflexivity. Qed.
