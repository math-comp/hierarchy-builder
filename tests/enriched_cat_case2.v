From HB Require Import structures.
From Coq Require Import ssreflect ssrfun.

(** Quiver *)

HB.mixin Record isQuiver Obj := { hom : Obj -> Obj -> Type }.

HB.structure Definition Quiver := { Obj of isQuiver Obj }.


(*************************************** OTHER MIXINS *************)
Require Import Coq.Program.Equality.
Require Import FunctionalExtensionality.

HB.mixin Record isMon T := {
    munit  : T;
    mop    : T -> T -> T;
    massoc : associative mop;
    mlid   : left_id munit mop;
    mrid   : right_id munit mop;
  }.
#[verbose]
HB.structure Definition Mon := { T of isMon T }.

HB.mixin Record isICAlg T := {
    aop   : T -> T -> T; 
    acomm : commutative aop; 
    aidem : idempotent aop; 
  }.
#[verbose]
HB.structure Definition ICAlg := { T of isICAlg T }.

HB.mixin Record isICMon T := {
    maunit  : T;
    aop    : T -> T -> T;
    maassoc : associative aop;
    malid   : left_id maunit aop;
    marid   : right_id maunit aop;
    macomm  : commutative aop; 
    maidem  : idempotent aop; 
  }.
#[verbose]
HB.structure Definition ICMon := { T of isICMon T & Mon T & ICAlg T }. 

(*
Lemma isICMon2isMon T : isICMon T -> isMon T.
  intro X.
  destruct X.
  econstructor; eauto.
Qed.

Lemma isICMon2isICAlg T : isICMon T -> isICAlg T.
  intro X.
  destruct X.
  econstructor; eauto.
Qed.
 *)

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
  { hom_isICMon_private : forall A B, isICMon (@hom T A B) }.
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

  HB.instance Definition b_A : isICAlg T :=
          isICAlg.Build T mop dum_comm dum_idem.
    
  HB.instance Definition b_M : isICMon T :=
    isICMon.Build T munit mop massoc mlid mrid dum_comm dum_idem.
   
HB.end.
