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

