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

(*
#[wrapper]
HB.mixin Record hom_isICAlg T of Quiver T :=
    { hom_isICAlg_private : forall A B, isICAlg (@hom T A B) }.

#[wrapper]
HB.mixin Record hom_isMon T of Quiver T :=
    { hom_isMon_private : forall A B, isMon (@hom T A B) }.

HB.structure
   Definition Mon_enriched_quiver :=
     { Obj of isQuiver Obj & hom_isMon Obj }.

HB.structure
   Definition ICAlg_enriched_quiver :=
     { Obj of isQuiver Obj & hom_isICAlg Obj }.
*)

#[wrapper]
HB.mixin Record hom_isICMon T of Quiver T :=
    { hom_isICMon_private : forall A B, ICMon (@hom T A B) }.
#[verbose]
HB.structure
   Definition ICMon_enriched_quiver :=
     { Obj of isQuiver Obj & hom_isICMon Obj }.

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

