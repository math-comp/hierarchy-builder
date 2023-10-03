From HB Require Import structures.
From Coq Require Import ssreflect ssrfun.

(** Quiver *)

HB.mixin Record isQuiver Obj := { hom : Obj -> Obj -> Type }.

HB.structure Definition Quiver := { Obj of isQuiver Obj }.


(*************************************** OTHER MIXINS *************)
Require Import Coq.Program.Equality.
Require Import FunctionalExtensionality.

HB.mixin Record isM T (munit: T) (mop: T -> T -> T) := {
    massoc : associative mop;
    mlid   : left_id munit mop;
    mrid   : right_id munit mop;
  }.

HB.mixin Record isMon T := {
    munit : T;
    mop   : T -> T -> T;
    mism   : isM T munit mop; 
  }.
#[verbose]
HB.structure Definition Mon := { T of isMon T }. 

HB.mixin Record isIC T (aop: T -> T -> T) := {
    comm : commutative aop; 
    idem : idempotent aop; 
  }.

HB.mixin Record isICAlg T := {
    aop : T -> T -> T;
    ica : isIC T aop ; 
  }.
#[verbose]
HB.structure Definition ICAlg := { T of isICAlg T }. 

HB.mixin Record isICMon T := {
    maunit  : T;
    maop    : T -> T -> T;
    mica    : isIC T maop;   
    mon     : isM T maunit maop;
  }.
HB.structure Definition ICMon := { T of isICMon T & Mon T & ICAlg T }. 


(*** wrapping ******************************************************)

#[wrapper]
HB.mixin Record hom_isMon T of Quiver T :=
    { hom_isMon_private : forall A B, isMon (@hom T A B) }.
#[verbose]
HB.structure Definition Mon_enriched_quiver :=
     { Obj of isQuiver Obj & hom_isMon Obj }.

#[wrapper]
HB.mixin Record hom_isICAlg T of Quiver T :=
    { hom_isICAlg_private : forall A B, isICAlg (@hom T A B) }.
#[verbose]
HB.structure Definition ICAlg_enriched_quiver :=
     { Obj of isQuiver Obj & hom_isICAlg Obj }.

#[wrapper]
HB.mixin Record hom_isICMon T of Quiver T :=
    { hom_isICMon_private : forall A B, isICMon (@hom T A B) }.
#[verbose]
HB.structure Definition ICMon_enriched_quiver :=
     { Obj of isQuiver Obj & hom_isICMon Obj }.

(*** factory ********************************************************)

HB.factory Record isMICAlg T of Mon T := {
    amop   : T -> T -> T;
    ameq   : forall x y, amop x y = mop x y;   
    amcomm : commutative amop; 
    amidem : idempotent amop; 
  }.

HB.builders Context T (f : isMICAlg T).

  Lemma amop_mop_eq : amop = mop.
    destruct f; simpl.
    eapply functional_extensionality; intro.
    eapply functional_extensionality; intro.
    auto.
  Qed.  
  
  Definition dum_comm :=
    @eq_rect (T -> T -> T) amop (@commutative T T) amcomm mop amop_mop_eq.

  Definition dum_idem :=
    @eq_rect (T -> T -> T) amop (@idempotent T) amidem mop amop_mop_eq.

  Definition b_A : isIC T mop :=
          isIC.Build T mop dum_comm dum_idem.

  HB.instance Definition bb_A : isICAlg T :=
          isICAlg.Build T mop b_A.
  
  Lemma mop_aop_eq (x y: T) : mop x y = aop x y.
    destruct f; auto.
  Qed.  

  Lemma b_M : isM T munit mop.
    destruct f.
    exact mism.
  Qed.  
  
  HB.instance Definition bb_M : isICMon T :=
    isICMon.Build T munit mop b_A b_M.

HB.end.

(**********************************************************************)

(** INSTANCE 1 *********************************************************

Object: Type,
Morphism: A -> option B 
Structure: Monoid (from isMon)
*)

HB.instance Definition funQ := isQuiver.Build Type 
   (fun A B => A -> option B).

Definition funQ_comp {A B: Type} (f g: hom A B) : hom A B :=
  fun x => 
  match f x with
  | Some _ => f x
  | _ => g x end.              

Definition funQ_zero {A B: Type} : hom A B :=
  fun (_:A) => None.

Program Definition funQ_isM (A B: Type) :
  isM (hom A B) funQ_zero funQ_comp :=
  isM.Build _ funQ_zero funQ_comp _ _ _.
Obligation 1.
   unfold associative; intros.
   unfold funQ_comp.
   eapply functional_extensionality; intro a; simpl.
   destruct (x a) eqn:K1.
   simpl; auto.
   destruct (y a); auto.
Qed.
Obligation 2.
   unfold left_id; intros.
   unfold funQ_comp; auto.
Qed.
Obligation 3.
   unfold right_id; simpl; intros.
   unfold funQ_zero, funQ_comp; simpl.
   eapply functional_extensionality; intro a.
   destruct (x a); auto.
Qed.

HB.instance Definition funQ_isMonoid (A B: Type) :
  isMon (hom A B) :=
  isMon.Build (hom A B) funQ_zero funQ_comp (funQ_isM A B).


(** INSTANCE 2 **********************************************

Object: ICMon.type
Morphism: ICMon.sort A -> ICMon.sort B
Structure: idempotent commutative monoid (by ICMon)
*)

#[verbose]
HB.instance Definition icmfunQ := 
  isQuiver.Build ICMon.type
    (fun A B => (ICMon.sort A) -> (ICMon.sort B)).             

Definition icmfunQ_comp {A B: ICMon.type} (f g: hom A B) : hom A B :=
  fun x => @maop B (f x) (g x).

Definition icmfunQ_zero {A B: ICMon.type} : hom A B := fun _ => @maunit B.

(* does not type-check without the Magma instance *)
Program Definition icmfunQ_isM (A B: ICMon.type) :
  isM (hom A B) (@icmfunQ_zero A B) (@icmfunQ_comp A B) :=
  isM.Build (hom A B) icmfunQ_zero icmfunQ_comp _ _ _.
Obligation 1.
unfold associative; simpl; intros.
unfold icmfunQ_comp; simpl; intros.
eapply functional_extensionality; intro x0.
destruct B eqn:B1.
destruct class eqn:class1.
destruct enriched_cat_case4_isMon_mixin eqn:C1.
simpl in *.
unfold maop; simpl.
unfold isICMon.maop; simpl.
destruct enriched_cat_case4_isICMon_mixin eqn:D1.
destruct mon0.
eapply massoc.
Qed.
Obligation 2.
unfold left_id; simpl; intros.
unfold icmfunQ_comp, icmfunQ_zero; simpl; intros.
eapply functional_extensionality; intro x0.
destruct B eqn: B1.
destruct class eqn: class1.
destruct enriched_cat_case4_isMon_mixin eqn:C1; simpl in *.
destruct mism0 eqn:mism1.
destruct enriched_cat_case4_isICMon_mixin eqn:D1; simpl in *. 
destruct mon0 eqn:mon1; simpl in *.
unfold maop; simpl.
eapply mlid0.
Qed.
Obligation 3.
unfold right_id; simpl; intros.
unfold icmfunQ_comp, icmfunQ_zero; simpl; intros.
eapply functional_extensionality; intro x0.
destruct B eqn: B1.
destruct class eqn: class1.
destruct enriched_cat_case4_isMon_mixin eqn:C1; simpl in *.
destruct mism0 eqn:mism1.
destruct enriched_cat_case4_isICMon_mixin eqn:D1; simpl in *. 
destruct mon0 eqn:mon1; simpl in *.
unfold maop; simpl.
eapply mrid0.
Qed.

HB.instance Definition icmfunQ_isMonoid (A B: ICMon.type) :
  isMon (hom A B) :=
  isMon.Build (hom A B) icmfunQ_zero icmfunQ_comp (icmfunQ_isM A B).



Program Definition icmfunQ_isICAlg (A B: ICMon.type) :
  isIC (hom A B) icmfunQ_comp := isIC.Build (hom A B) icmfunQ_comp _ _.
Obligation 1.
unfold commutative; simpl; intros.
unfold icmfunQ_comp; simpl; intros.
eapply functional_extensionality; intro x0.
destruct B.
destruct class.
destruct enriched_cat_case4_isICAlg_mixin.
unfold mop; simpl.
destruct enriched_cat_case4_isMon_mixin.
simpl.
simpl in x.
simpl in *.
destruct ica0.
eapply comm; auto.
Qed.
Obligation 2.
unfold idempotent, mop; simpl; intros.
unfold icmfunQ_comp; simpl; intros.
eapply functional_extensionality; intro x0.
destruct B.
destruct class.
destruct enriched_cat_case1_isICMon_mixin.
simpl in *.
destruct ica0.
eapply aidem0; auto.
Qed.

Program Definition icmfunQ_isICMon (A B: ICMon.type) :
  isICMon (hom A B) := isICMon.Build (hom A B) _ _.
Obligation 1.
eapply icmfunQ_isICAlg.
Qed.
Obligation 2.
eapply icmfunQ_isMon.
Qed.

Fail HB.instance Definition icmfunQ_isMonoid (A B: ICMon.type) :
  isMon (hom A B) := icmfunQ_isMon A B.

Fail HB.instance Definition icmfunQ_isICAlgebra (A B: ICMon.type) :
  isICAlg (hom A B) := icmfunQ_isICAlg A B.

Fail HB.instance Definition icmfunQ_isICMonoid (A B: ICMon.type) :
  isICMon (hom A B) := icmfunQ_isICMon A B.

