From HB Require Import structures.
From Coq Require Import ssreflect ssrfun.

(** Quiver *)

HB.mixin Record isQuiver Obj := { hom : Obj -> Obj -> Type }.

HB.structure Definition Quiver := { Obj of isQuiver Obj }.

(** Ohter base mixins *)

HB.mixin Record isMon A := {
    zero  : A;
    add   : A -> A -> A;
    addrA : associative add;
    add0r : left_id zero add;
    addr0 : right_id zero add;
  }.

HB.mixin Record isIAlg A := {
    iadd : A -> A -> A; 
    iaddI : idempotent iadd; 
  }.

HB.mixin Record isCAlg A := {
    cadd : A -> A -> A; 
    caddrC : commutative cadd; 
  }.

(** Base structures *)

HB.structure Definition Monoid := { A of isMon A }.

HB.structure Definition CAlgebra := { A of isCAlg A }.

HB.structure Definition IAlgebra := { A of isIAlg A }.

(** Complex mixins *)

(*******************************************************************)
(********** Combining mixins ***************************************)

(***** Vanilla Coq (no HB) *)

Record isMon0 A := {
    zero0  : A;
    add0   : A -> A -> A;
    addrA0 : associative add0;
    add0r0 : left_id zero0 add0;
    addr00 : right_id zero0 add0;
  }.

Record isIAlg0 A := {
    iadd0 : A -> A -> A; 
    iaddI0 : idempotent iadd0; 
  }.

Record isIMon0 A := { is_mon0 : isMon0 A;
                      is_ialg0 : isIAlg0 A;
                      mon_ialg_ch0 : add0 _ is_mon0 = iadd0 _ is_ialg0 ;
  }.


(***** The analogous of vanilla does not work in HB *)

Fail HB.mixin Record isIMonM A := { is_mon : isMon A;
                               is_ialg : isIAlg A; 
                               mon_ialg_ch : add _ is_mon = iadd _ is_ialg ;
  }.

Fail HB.mixin Record isIMonS A := { is_mon : Monoid A;
                               is_ialg : IAlgebra A; 
                               mon_ialg_ch : add _ is_mon = iadd _ is_ialg ;
  }.

(***** Basic approach (can be cumbersome) *)

HB.mixin Record isIMonB A := {
    zero  : A;
    add   : A -> A -> A;
    addrA : associative add;
    add0r : left_id zero add;
    addr0 : right_id zero add;
    addI : idempotent add; 
}.

HB.mixin Record isCMonB A := {
    zero  : A;
    add   : A -> A -> A;
    addrA : associative add;
    add0r : left_id zero add;
    addr0 : right_id zero add;
    addC : commutative add; 
}.


(***** Operator mixins *)

(** single dependent pair parameter *)

HB.mixin Record isOpMon1 (S: sigT (fun A => A -> A -> A)) := {
    zero  : projT1 S;
    addrA : associative (projT2 S);
    add0r : left_id zero (projT2 S);
    addr0 : right_id zero (projT2 S);
  }.

HB.structure Definition OpMonoid1 := { C of isOpMon1 C }.

HB.mixin Record isOpIAlg1 (S: sigT (fun A => A -> A -> A)) := {
    addI : idempotent (projT2 S);
  }.

HB.structure Definition OpIAlgebra1 := { C of isOpIAlg1 C }.

HB.mixin Record isOpIMon1 A of OpMonoid1 A & OpIAlgebra1 A. 


(** two parameters (subject is Add) *)

(**)
HB.mixin Record isOpMon2 A (Add: A -> A -> A) (Zero: A) := {
    addrA : associative Add;
    add0r : left_id Zero Add;
    addr0 : right_id Zero Add;
  }.

(* HB.structure Definition OpMon2 A := { Add of isOpMon2 A Add }. *)

HB.mixin Record isOpMonoid2 A := { add: A -> A -> A;
                                   zero: A;
                                   is_op_mon : isOpMon2 A add zero }.

HB.structure Definition OpMonoid2 := { A of isOpMonoid2 A }.

(**)
HB.mixin Record isOpIAlg2 A (Add: A -> A -> A) := {
    addI : idempotent Add;
  }.

HB.mixin Record isOpIAlgebra2 A := { add: A -> A -> A;
                                     is_op_ialg : isOpIAlg2 A add }.

HB.structure Definition OpIAlgebra2 := { A of isOpIAlgebra2 A }.

(**)
HB.mixin Record isOpCAlg2 A (Add: A -> A -> A) := {
    addC : commutative Add;
  }.

HB.mixin Record isOpCAlgebra2 A := { add: A -> A -> A;
                                     is_op_calg : isOpCAlg2 A add }.

HB.structure Definition OpCAlgebra2 := { A of isOpCAlgebra2 A }.

(**)
HB.mixin Record isOpIMon2 A (Add: A -> A -> A) (Zero: A) := {
    is_op_mon : isOpMon2 A Add Zero ;
    is_op_ialg : isOpIAlg2 A Add ;
  }.  

HB.mixin Record isOpIMonoid2 A := { add: A -> A -> A;
                                    zero: A;
                                    is_op_imon : isOpIMon2 A add zero }.

HB.structure Definition OpIMonoid2 := { A of isOpIMonoid2 A }.

(**)
HB.mixin Record isOpCMon2 A (Add: A -> A -> A) (Zero: A) := {
    is_op_mon : isOpMon2 A Add Zero ;
    is_op_calg : isOpCAlg2 A Add ;
  }.  

HB.mixin Record isOpCMonoid2 A := { add: A -> A -> A;
                                    zero: A;
                                    is_op_imon : isOpCMon2 A add zero }.

HB.structure Definition OpCMonoid2 := { A of isOpCMonoid2 A }.

(**)
HB.mixin Record isOpCIAlg2 A (Add: A -> A -> A) := {
    is_op_ialg : isOpIAlg2 A Add ;
    is_op_calg : isOpCAlg2 A Add ;
  }.  

HB.mixin Record isOpCIAlgebra2 A := { add: A -> A -> A;
                                  is_op_icalg : isOpCIAlg2 A add }.

HB.structure Definition OpCIAlgebra2 := { A of isOpCIAlgebra2 A }.

(**)
HB.mixin Record isOpICAlg2 A (Add: A -> A -> A) := {
    is_op_calg : isOpCAlg2 A Add ;
    is_op_ialg : isOpIAlg2 A Add ;
  }.

HB.mixin Record isOpICAlgebra2 A := { add: A -> A -> A;
                                     is_op_calg : isOpICAlg2 A add }.

HB.structure Definition OpICAlgebra2 := { A of isOpICAlgebra2 A }.

(**)
HB.mixin Record isOpCIMon2 A (Add: A -> A -> A) (Zero: A) := {
    is_op_mon : isOpIMon2 A Add Zero ;
    is_op_calg : isOpCAlg2 A Add ;
  }.  

HB.mixin Record isOpCIMonoid2 A := { add: A -> A -> A;
                                     zero: A;
                                     is_op_cimon : isOpCIMon2 A add zero }.

HB.structure Definition OpCIMonoid2 := { A of isOpCIMonoid2 A }.

(**)
HB.mixin Record isOpICMon2 A (Add: A -> A -> A) (Zero: A) := {
    is_op_mon : isOpCMon2 A Add Zero ;
    is_op_calg : isOpIAlg2 A Add ;
  }.  

HB.mixin Record isOpICMonoid2 A := { add: A -> A -> A;
                                     zero: A;
                                     is_op_cimon : isOpICMon2 A add zero }.

HB.structure Definition OpICMonoid2 := { A of isOpICMonoid2 A }.


(*******************************************************************)

(** Wrapper mixins *)

#[wrapper]
HB.mixin Record hom_isMon T of Quiver T :=
    { hom_isMon_private : forall A B, isOpMonoid2 (@hom T A B) }.

#[wrapper]
HB.mixin Record hom_isIAlg T of Quiver T :=
    { hom_isIAlg_private : forall A B, isOpIAlgebra2 (@hom T A B) }.

#[wrapper]
HB.mixin Record hom_isCAlg T of Quiver T :=
    { hom_isCAlg_private : forall A B, isOpCAlgebra2 (@hom T A B) }.

#[wrapper]
HB.mixin Record hom_isIMon T of Quiver T :=
    { hom_isIMon_private : forall A B, isOpIMonoid2 (@hom T A B) }.

#[wrapper]
HB.mixin Record hom_isCMon T of Quiver T :=
    { hom_isCMon_private : forall A B, isOpCMonoid2 (@hom T A B) }.

#[wrapper]
HB.mixin Record hom_isCIAlg T of Quiver T :=
    { hom_isCIAlg_private : forall A B, isOpCIAlgebra2 (@hom T A B) }.

#[wrapper]
HB.mixin Record hom_isICAlg T of Quiver T :=
    { hom_isICAlg_private : forall A B, isOpICAlgebra2 (@hom T A B) }.

#[wrapper]
HB.mixin Record hom_isCIMon T of Quiver T :=
    { hom_isCIMon_private : forall A B, isOpCIMonoid2 (@hom T A B) }.

#[wrapper]
HB.mixin Record hom_isICMon T of Quiver T :=
    { hom_isICMon_private : forall A B, isOpICMonoid2 (@hom T A B) }.


(** Base enriched structures *)

HB.structure
   Definition Monoid_enriched_quiver :=
     { Obj of isQuiver Obj & hom_isMon Obj }.
     
HB.structure
   Definition IAlgebra_enriched_quiver :=
     { Obj of isQuiver Obj & hom_isIAlg Obj }.
     
HB.structure
   Definition CAlgebra_enriched_quiver :=
     { Obj of isQuiver Obj & hom_isCAlg Obj }.

(** Complex enriched structures *)

HB.structure
   Definition IMonoid_enriched_quiver :=
     { Obj of isQuiver Obj & hom_isMon Obj & hom_isIAlg Obj}.

HB.structure
   Definition CIAlgebra_enriched_quiver :=
     { Obj of isQuiver Obj & hom_isIAlg Obj & hom_isCAlg Obj}.

HB.structure
   Definition CIMonoid_enriched_quiver :=
     { Obj of isQuiver Obj & hom_isMon Obj & hom_isIAlg Obj & hom_isCAlg Obj}.

(********* INSTANCES *****************************)

Require Import FunctionalExtensionality.

(** SAMPLE INSTANCE 1 *)

HB.instance Definition funQ := isQuiver.Build Type 
   (fun A B => A -> option B).

Definition funQ_comp {A B: Type} (f g: hom A B) : hom A B :=
  fun x => 
  match f x with
  | Some _ => f x
  | _ => g x end.              

Program Definition funQ_isMon (A B: Type) :
  isOpMon2 (hom A B) funQ_comp (fun (_:A) => None) :=
  isOpMon2.Build _ _ (fun (_:A) => None) _ _ _.
Obligation 1.
unfold associative; intros.
eapply functional_extensionality; intro a.
unfold funQ_comp.
destruct (x a) eqn:K1.
simpl; auto.
destruct (y a); auto.
Qed.
Obligation 2.
unfold left_id; intros.
unfold funQ_comp; auto.
Qed.
Obligation 3.
unfold right_id; intros.
eapply functional_extensionality; intro a.
unfold funQ_comp.
destruct (x a); auto.
Qed.

Program Definition funQ_isIAlg (A B: Type) :
  isOpIAlg2 (hom A B) funQ_comp :=
  isOpIAlg2.Build _ _ _.
Obligation 1.
unfold idempotent; intros.
eapply functional_extensionality; intro a.
unfold funQ_comp.
destruct (x a); auto.
Qed.

Program Definition funQ_isIMon (A B: Type) :
  isOpIMon2 (hom A B) funQ_comp (fun (_:A) => None) :=
  isOpIMon2.Build (hom A B) _ _ _ _.
Obligation 1.
eapply funQ_isMon.
Qed.
Obligation 2.
eapply funQ_isIAlg.
Qed.

HB.instance Definition funQ_isMonoid (A B: Type) :
  isOpMonoid2 (hom A B) :=
  isOpMonoid2.Build (hom A B) funQ_comp (fun (_:A) => None) (funQ_isMon A B).

HB.instance Definition funQ_isIAlgebra (A B: Type) :
  isOpIAlgebra2 (hom A B) :=
  isOpIAlgebra2.Build (hom A B) funQ_comp (funQ_isIAlg A B).

HB.instance Definition funQ_isIMonoid (A B: Type) :
  isOpIMonoid2 (hom A B) :=
  isOpIMonoid2.Build (hom A B) funQ_comp (fun (_:A) => None)
    (funQ_isIMon A B).

Elpi Print HB.structure.


(** SAMPLE INSTANCE 2 *)

Lemma zero_unique {B} (X: B -> B -> B) (zz0 zz1:B) :
  left_id zz0 X -> right_id zz0 X -> left_id zz1 X -> right_id zz1 X ->
  zz0 = zz1.
  unfold left_id, right_id.
  intros.
  specialize (H0 zz1).
  specialize (H1 zz0).
  rewrite H1 in H0.
  auto.
Qed.

Open Scope type.

HB.instance Definition cmfunQ := 
  isQuiver.Build (sigT (fun A => (A -> A -> A) * A))
    (fun X Y => isOpCMon2 (projT1 X) (fst (projT2 X)) (snd (projT2 X)) ->
                isOpCMon2 (projT1 Y) (fst (projT2 Y)) (snd (projT2 Y)) ->
                (projT1 X) -> (projT1 Y)).

Definition cmfunQ_comp {A B: sigT (fun A => (A -> A -> A) * A)} 
  (f g: @hom _ A B) : hom A B :=
  fun (ca: isOpCMon2 (projT1 A) (fst (projT2 A)) (snd (projT2 A)))
      (cb: isOpCMon2 (projT1 B) (fst (projT2 B)) (snd (projT2 B))) a => 
  match (f ca cb a, g ca cb a) with
  | (b1, b2) => (fst (projT2 B)) b1 b2 end.              

Program Definition cmfunQ_zero {A B: sigT (fun A => (A -> A -> A) * A)} :
  hom A B.
Proof.
  unfold hom; intros.
  unfold isQuiver.hom.
  unfold Quiver.cmonoid_enriched_cat_isQuiver_mixin.
  unfold Quiver.class.
  simpl; intros.
  destruct B as [X [f x1]]; simpl.
  exact x1.
Defined.  
    
Program Definition cmfunQ_isCMon (A B: sigT (fun A => (A -> A -> A) * A)) :
  isOpCMon2 (hom A B) cmfunQ_comp cmfunQ_zero :=
  isOpCMon2.Build (hom A B) cmfunQ_comp _ _ _.
Obligation 1.
unfold cmfunQ_comp; simpl.
econstructor.
{- unfold associative; intros.
   eapply functional_extensionality; intro CMa.
   eapply functional_extensionality; intro CMb.
   eapply functional_extensionality; intro v.
   remember CMb as CMb1.
   destruct CMb.
   destruct is_op_mon0.
   unfold associative in addrA1.
   simpl in addrA1.
   eapply addrA1.
}
{- unfold left_id; intros.
   eapply functional_extensionality; intro CMa.
   eapply functional_extensionality; intro CMb.
   eapply functional_extensionality; intro v.
   remember CMb as CMb1.
   destruct CMb.
   destruct is_op_mon0.
   unfold left_id in add0r1.
   simpl in add0r1.
   unfold cmfunQ_zero.
   eapply add0r1.
}
{- unfold right_id; intros.
   eapply functional_extensionality; intro CMa.
   eapply functional_extensionality; intro CMb.
   eapply functional_extensionality; intro v.
   remember CMb as CMb1.
   destruct CMb.
   destruct is_op_mon0.
   unfold right_id in addr1.
   simpl in addr1.
   unfold cmfunQ_zero.
   eapply addr1.
}
Qed.
Obligation 2.
   econstructor.
   unfold cmfunQ_comp.
   unfold commutative; simpl; intros.
   eapply functional_extensionality; intro CMa.
   eapply functional_extensionality; intro CMb.
   eapply functional_extensionality; intro v.
   remember CMb as CMb1.
   destruct CMb.
   destruct is_op_calg0.
   simpl in addC.
   eapply addC.
Qed.   

HB.instance Definition cmfunQ_isMonoid
  (A B: sigT (fun A => (A -> A -> A) * A)) :
  isOpCMonoid2 (hom A B) :=
  isOpCMonoid2.Build (hom A B) cmfunQ_comp cmfunQ_zero (cmfunQ_isCMon A B).

Elpi Print HB.structure.



(** SAMPLE INSTANCE 3 *)

HB.instance Definition cimfunQ := 
  isQuiver.Build (sigT (fun A => A -> A -> A))
    (fun X Y => isOpCIAlg2 (projT1 X) (projT2 X) ->
                isOpCIAlg2 (projT1 Y) (projT2 Y) ->
                (projT1 X) -> option (projT1 Y)).

Definition cimfunQ_comp {A B: sigT (fun A => A -> A -> A)} 
  (f g: hom A B) : hom A B :=
  fun (ca: isOpCIAlg2 (projT1 A) (projT2 A))
      (cb: isOpCIAlg2 (projT1 B) (projT2 B)) a => 
    match (f ca cb a, g ca cb a) with
    | (Some b1, Some b2) => Some (projT2 B b1 b2)
    | (Some b, None) => Some b
    | (None, Some b) => Some b                        
    | _ => None end.              

Definition cimfunQ_zero {A B: sigT (fun A => A -> A -> A)} : hom A B := 
  fun _ _ _ => None.

(*
Program Definition funQ_isCIMon (A B: sigT (fun A => A -> A -> A)) :
  isOpCIMon2 (hom A B) cimfunQ_comp cimfunQ_zero :=
  isOpCIMon2.Build _ _ cimfunQ_zero _ _.
Obligation 1.
econstructor.
econstructor.
unfold associative; intros.
eapply functional_extensionality; intro ca.
eapply functional_extensionality; intro cb.
eapply functional_extensionality; intro v.
unfold cimfunQ_comp.
destruct (x ca cb v) eqn:K1.
simpl; auto.
destruct (y ca cb v); auto.
destruct (z ca cb v); auto.
destruct cb. 
Qed.
*)

