From HB Require Import structures.
From Coq Require Import ssreflect ssrfun.

(** Quiver *)

HB.mixin Record isQuiver Obj := { hom : Obj -> Obj -> Type }.

HB.structure Definition Quiver := { Obj of isQuiver Obj }.


(*************************************** OTHER MIXINS *************)
Require Import Coq.Program.Equality.
Require Import FunctionalExtensionality.

HB.mixin Record isMagma T := {
    mop    : T -> T -> T;
}.
HB.structure Definition Magma := { T of isMagma T }.

HB.mixin Record isMon T of isMagma T := {
    munit  : T;
    massoc : associative (mop : T -> T -> T);
    mlid   : left_id munit mop;
    mrid   : right_id munit mop;
  }.
#[verbose]
HB.structure Definition Mon := { T of isMon T }.

HB.mixin Record isICAlg T of isMagma T := {
    acomm : commutative (mop : T -> T -> T); 
    aidem : idempotent (mop : T -> T -> T); 
  }.
#[verbose]
HB.structure Definition ICAlg := { T of isICAlg T }.

HB.mixin Record isICMon T of isMagma T := {
    ica: isICAlg T ;
    mon: isMon T;
  }.
#[verbose]
HB.structure Definition ICMon := { T of isICMon T }. 


(*****  wrapping ****************************************************)

#[wrapper]
HB.mixin Record hom_isMagma T of Quiver T :=
    { hom_isMagma_private : forall A B, isMagma (@hom T A B) }.
HB.structure
   Definition Magma_enriched_quiver :=
     { Obj of isQuiver Obj & hom_isMagma Obj }.

(*
#[wrapper]
HB.mixin Record hom_isMon T of Quiver T :=
    { hom_isMon_private : forall A B, Mon (@hom T A B) }.
*)
(* need to add explicitly Magma_enriched_quiver, otherwise switch 
   from mixin to structure *)
#[wrapper]
HB.mixin Record hom_isMon T of Quiver T & Magma_enriched_quiver T :=
    { hom_isMon_private : forall A B, isMon (@hom T A B) }.
HB.structure
   Definition Mon_enriched_quiver :=
     { Obj of isQuiver Obj & hom_isMon Obj }.

#[wrapper]
HB.mixin Record hom_isICAlg T of Quiver T & Magma_enriched_quiver T :=
    { hom_isICAlg_private : forall A B, isICAlg (@hom T A B) }.
HB.structure
   Definition ICAlg_enriched_quiver :=
     { Obj of isQuiver Obj & hom_isICAlg Obj }.

#[wrapper]
HB.mixin Record hom_isICMon T of Quiver T & Magma_enriched_quiver T :=
    { hom_isICMon_private : forall A B, isICMon (@hom T A B) }.
#[verbose]
HB.structure
   Definition ICMon_enriched_quiver :=
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

  HB.instance Definition b_Mg : isMagma T :=
          isMagma.Build T mop.
    
  HB.instance Definition b_IC : isICAlg T :=
          isICAlg.Build T dum_comm dum_idem.

  Lemma M : isMon T.
    destruct f; auto.
  Qed.  
  
  HB.instance Definition b_M : isICMon T :=
    isICMon.Build T b_IC M.
   
HB.end.

(*******************************************************************)

(** INSTANCE 1 ***********************************************

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

(* does not work without declaring the Magma wrapper *)
HB.instance Definition funQ_isMagma (A B: Type) :
  isMagma (hom A B) := isMagma.Build _ funQ_comp. 

Program Definition funQ_isMon (A B: Type) : isMon (hom A B) :=
  isMon.Build _ funQ_zero _ _ _.
Obligation 1.
   unfold associative; intros.
   eapply functional_extensionality; intro a.
   unfold mop; simpl.
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
   unfold right_id, mop; simpl; intros.
   unfold funQ_zero, funQ_comp; simpl.
   eapply functional_extensionality; intro a.
   destruct (x a); auto.
Qed.

HB.instance Definition funQ_Monoid (A B: Type) :
  isMon (hom A B) := funQ_isMon A B.

 
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
  fun x => @mop B (f x) (g x).

Definition icmfunQ_zero {A B: ICMon.type} : hom A B.
  destruct B.
  unfold hom; simpl; intro.
  destruct class.
  destruct enriched_cat_case1_isICMon_mixin.
  destruct mon0.
  exact munit0.
Defined.  

(* does not work without declaring the Magma wrapper *)
HB.instance Definition icmfunQ_isMagma (A B: ICMon.type) :
  isMagma (hom A B) := isMagma.Build _ icmfunQ_comp. 

(* does not type-check without the Magma instance *)
Program Definition icmfunQ_isMon (A B: ICMon.type) :
  isMon (hom A B) := isMon.Build (hom A B) icmfunQ_zero _ _ _.
Obligation 1.
unfold associative, mop; simpl; intros.
unfold icmfunQ_comp; simpl; intros.
eapply functional_extensionality; intro x0.
destruct B.
destruct class.
destruct enriched_cat_case1_isICMon_mixin.
simpl in *.
destruct mon0.
eapply massoc0; auto.
Qed.
Obligation 2.
unfold left_id, mop; simpl; intros.
unfold icmfunQ_comp, icmfunQ_zero; simpl; intros.
eapply functional_extensionality; intro x0.
destruct B.
destruct class.
destruct enriched_cat_case1_isICMon_mixin.
destruct mon0.
auto.
Qed.
Obligation 3.
unfold right_id, mop; simpl; intros.
unfold icmfunQ_comp, icmfunQ_zero; simpl; intros.
eapply functional_extensionality; intro x0.
destruct B.
destruct class.
destruct enriched_cat_case1_isICMon_mixin.
destruct mon0.
auto.
Qed.

Program Definition icmfunQ_isICAlg (A B: ICMon.type) :
  isICAlg (hom A B) := isICAlg.Build (hom A B) _ _.
Obligation 1.
unfold commutative, mop; simpl; intros.
unfold icmfunQ_comp; simpl; intros.
eapply functional_extensionality; intro x0.
destruct B.
destruct class.
destruct enriched_cat_case1_isICMon_mixin.
simpl in *.
destruct ica0.
eapply acomm0; auto.
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

