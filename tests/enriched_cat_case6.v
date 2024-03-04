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

HB.mixin Record isCAlg T of isMagma T := {
    acomm : commutative (mop : T -> T -> T); 
  }.
#[verbose]
HB.structure Definition CAlg := { T of isCAlg T }.

HB.mixin Record isIAlg T of isMagma T := { 
    aidem : idempotent (mop : T -> T -> T); 
  }.
#[verbose]
HB.structure Definition IAlg := { T of isIAlg T }.

(* HB.mixin Record isICAlg T of isMagma T & IAlg T & CAlg T := {
 }. *)
#[verbose]
HB.structure Definition ICAlg := { T of CAlg T & IAlg T }.

(* HB.mixin Record isCMon T of isMagma T := {
    cca: isCAlg T ;
    cmon: isMon T;
  }. *)
#[verbose]
HB.structure Definition CMon := { T of Mon T & CAlg T }. 

(*
HB.mixin Record isIMon T of isMagma T := {
    iia: isIAlg T ;
    imon: isMon T;
  }. *)
#[verbose]
HB.structure Definition IMon := { T of Mon T & IAlg T }. 

(*
HB.mixin Record isICMon T of isMagma T := {
    ica: isICAlg T ;
    mon: isMon T;
  }.
*)
#[verbose]
HB.structure Definition ICMon := { T of IMon T & CMon T }. 


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
HB.mixin Record hom_isMon T of Magma_enriched_quiver T :=
    { hom_isMon_private : forall A B, isMon (@hom T A B) }.
HB.structure
   Definition Mon_enriched_quiver :=
     { Obj of isQuiver Obj & hom_isMon Obj }.

#[wrapper]
HB.mixin Record hom_isCAlg T of Magma_enriched_quiver T :=
    { hom_isCAlg_private : forall A B, isCAlg (@hom T A B) }.
HB.structure
   Definition CAlg_enriched_quiver :=
     { Obj of isQuiver Obj & hom_isCAlg Obj }.

#[wrapper]
HB.mixin Record hom_isIAlg T of Magma_enriched_quiver T :=
    { hom_isIAlg_private : forall A B, isIAlg (@hom T A B) }.
HB.structure
   Definition IAlg_enriched_quiver :=
     { Obj of isQuiver Obj & hom_isIAlg Obj }.

(*
#[wrapper]
HB.mixin Record hom_isICAlg T of Magma_enriched_quiver T :=
    { hom_isICAlg_private : forall A B, isICAlg (@hom T A B) }.
HB.structure
   Definition ICAlg_enriched_quiver :=
     { Obj of isQuiver Obj & hom_isICAlg Obj }.

#[wrapper]
HB.mixin Record hom_isCMon T of Magma_enriched_quiver T :=
    { hom_isCMon_private : forall A B, isCMon (@hom T A B) }.
#[verbose]
HB.structure
   Definition CMon_enriched_quiver :=
     { Obj of isQuiver Obj & hom_isCMon Obj }.

#[wrapper]
HB.mixin Record hom_isIMon T of Magma_enriched_quiver T :=
    { hom_isIMon_private : forall A B, isIMon (@hom T A B) }.
*)
#[verbose]
HB.structure
   Definition IMon_enriched_quiver :=
     { Obj of Mon_enriched_quiver Obj & IAlg_enriched_quiver Obj }.

#[wrapper=false]
HB.instance Definition _ (T : IMon_enriched_quiver.type) A B : isMon (@hom T A B) :=
  Mon.on (@hom T A B).

(****)

#[verbose]
HB.structure
   Definition CMon_enriched_quiver :=
     { Obj of Mon_enriched_quiver Obj & CAlg_enriched_quiver Obj }.


#[wrapper=false]
HB.instance Definition _ (T : CMon_enriched_quiver.type) A B :=
  Mon.on (@hom T A B).

(*     { Obj of isQuiver Obj & hom_isMon Obj & hom_isIAlg Obj }. *)

(*
#[wrapper]
HB.mixin Record hom_isICMon T of Magma_enriched_quiver T :=
    { hom_isICMon_private : forall A B, isICMon (@hom T A B) }.
#[verbose]
HB.structure
   Definition ICMon_enriched_quiver :=
     { Obj of isQuiver Obj & hom_isICMon Obj }.
*)

(*** factory ********************************************************)

HB.factory Record isMICAlg T of Mon T := {
    amop   : T -> T -> T;
    ameq   : forall x y, amop x y = mop x y;   
    amcomm : commutative amop; 
    amidem : idempotent amop; 
  }.

HB.builders Context T (_ : isMICAlg T).

  Lemma amop_mop_eq : amop = mop.
   (* destruct f; simpl. *)
    eapply functional_extensionality; intro.
    eapply functional_extensionality; intro.
    apply ameq.
  Qed.  
  
  Definition dum_comm :=
    @eq_rect (T -> T -> T) amop (@commutative T T) amcomm mop amop_mop_eq.

  Definition dum_idem :=
    @eq_rect (T -> T -> T) amop (@idempotent T) amidem mop amop_mop_eq.
   
  HB.instance Definition b_C : isCAlg T :=
          isCAlg.Build T dum_comm.

  HB.instance Definition b_I : isIAlg T :=
          isIAlg.Build T dum_idem.

  (*
  HB.instance Definition b_IC : isICAlg T :=
          isICAlg.Build T b_C b_I.
  *)
(*
  Lemma M : isMon T.
    auto.
  Qed.  
*)
  (*
  HB.instance Definition b_M : isICMon T :=
    isICMon.Build T b_IC M.
   *)   

HB.end.

(*******************************************************************)

(** INSTANCE 1 ***********************************************

Object: Type,
Morphism: A -> option B 
Structure: Monoid (from isMon)
*)

HB.instance Definition funQ := isQuiver.Build Type 
   (fun A B => A -> option B).

Check Type : Quiver.type.

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

Program Definition funQ_isIAlg (A B: Type) :
  isIAlg (hom A B) := isIAlg.Build _ _.
Obligation 1.
unfold idempotent; intros.
eapply functional_extensionality; intro a.
unfold mop; simpl.
unfold funQ_comp; simpl.
destruct (x a); auto.
Qed.

(*
Program Definition funQ_isIMon (A B: Type) :
  isIMon (hom A B) := isIMon.Build (hom A B) _ _.
Obligation 1.
eapply funQ_isIAlg.
Qed.
Obligation 2.
eapply funQ_isMon.
Qed.
*)

#[verbose]
HB.instance Definition funQ_IAlgebra (A B: Type) :
  isIAlg (hom A B) := funQ_isIAlg A B.

#[verbose]
HB.instance Definition funQ_Monoid (A B: Type) :
  isMon (hom A B) := funQ_isMon A B.

Check hom (nat:Type) nat : IMon.type.

(***)

HB.graph "foo.dot".

Definition hom' (A B: Type) := hom A B.

HB.instance Definition _ (A B: Type) := Mon.on (hom' A B).
HB.instance Definition _ (A B: Type) := IAlg.on (hom' A B).

Check hom' (nat:Type) nat : IMon.type.

HB.instance Definition _ (A B: Type) := Mon.on (hom' A B).
          

(** INSTANCE 2 **********************************************

Object: CMon.type
Morphism: CMon.sort A -> CMon.sort B
Structure: commutative monoid (by CMon)
*)

#[verbose]
HB.instance Definition cmfunQ := 
  isQuiver.Build CMon.type
    (fun A B => (CMon.sort A) -> (CMon.sort B)).             

Definition cmfunQ_comp {A B: CMon.type} (f g: hom A B) : hom A B :=
  fun x => @mop B (f x) (g x).

Definition cmfunQ_zero {A B: CMon.type} : hom A B := fun a : A => munit.

(* does not work without declaring the Magma wrapper *)
HB.instance Definition cmfunQ_isMagma (A B: CMon.type) :
  isMagma (hom A B) := isMagma.Build _ cmfunQ_comp. 

(* does not type-check without the Magma instance *)
Program Definition cmfunQ_isMon (A B: CMon.type) :
  isMon (hom A B) := isMon.Build (hom A B) cmfunQ_zero _ _ _.
Obligation 1.
unfold associative, mop; simpl; intros.
unfold cmfunQ_comp; simpl; intros.
eapply functional_extensionality; intro x0.
refine  (massoc _ _ _).
Qed.
Obligation 2.
unfold left_id, mop; simpl; intros.
unfold cmfunQ_comp, cmfunQ_zero; simpl; intros.
eapply functional_extensionality; intro x0.
refine (mlid _).
Qed.
Obligation 3.
unfold right_id, mop; simpl; intros.
unfold cmfunQ_comp, cmfunQ_zero; simpl; intros.
eapply functional_extensionality; intro x0.
refine (mrid _).
Qed.

Program Definition cmfunQ_isCAlg (A B: CMon.type) :
  isCAlg (hom A B) := isCAlg.Build (hom A B) _.
Obligation 1.
unfold commutative, mop; simpl; intros.
unfold cmfunQ_comp; simpl; intros.
eapply functional_extensionality; intro x0.
refine (acomm _ _).
Qed.

HB.instance Definition cmfunQ_isMonoid (A B: CMon.type) :
  isMon (hom A B) := cmfunQ_isMon A B.

HB.instance Definition cmfunQ_isICAlgebra (A B: CMon.type) :
  isCAlg (hom A B) := cmfunQ_isCAlg A B.

(*
HB.instance Definition icmfunQ_isCMonoid (A B: CMon.type) :
  isCMon (hom A B) := cmfunQ_isCMon A B.

Check CMon.type : CAlg_enriched_quiver.type.
*)

(*********************************************************)

(*
Object: IMon.type
Morphism: IMon.sort A -> IMon.sort B
Structure: idempotent monoid (by IMon)
*)

#[verbose]
HB.instance Definition imfunQ := 
  isQuiver.Build IMon.type
    (fun A B => (IMon.sort A) -> (IMon.sort B)).             

Definition imfunQ_comp {A B: IMon.type} (f g: hom A B) : hom A B :=
  fun x => @mop B (f x) (g x).

Definition imfunQ_zero {A B: IMon.type} : hom A B := fun a : A => munit.

(* does not work without declaring the Magma wrapper *)
HB.instance Definition imfunQ_isMagma (A B: IMon.type) :
  isMagma (hom A B) := isMagma.Build _ imfunQ_comp. 

(* does not type-check without the Magma instance *)
Program Definition imfunQ_isMon (A B: IMon.type) :
  isMon (hom A B) := isMon.Build (hom A B) imfunQ_zero _ _ _.
Obligation 1.
unfold associative, mop; simpl; intros.
unfold imfunQ_comp; simpl; intros.
eapply functional_extensionality; intro x0.
refine (massoc _ _ _).
Qed.
Obligation 2.
unfold left_id, mop; simpl; intros.
unfold imfunQ_comp, imfunQ_zero; simpl; intros.
eapply functional_extensionality; intro x0.
refine (mlid _).
Qed.
Obligation 3.
unfold right_id, mop; simpl; intros.
unfold imfunQ_comp, imfunQ_zero; simpl; intros.
eapply functional_extensionality; intro x0.
refine (mrid _).
Qed.

Program Definition imfunQ_isIAlg (A B: IMon.type) :
  isIAlg (hom A B) := isIAlg.Build (hom A B) _.
Obligation 1.
unfold idempotent, mop; simpl; intros.
unfold imfunQ_comp; simpl; intros.
eapply functional_extensionality; intro x0.
refine (aidem _).
Qed.

HB.instance Definition imfunQ_isMonoid (A B: IMon.type) :
  isMon (hom A B) := imfunQ_isMon A B.

HB.instance Definition imfunQ_isIAlgebra (A B: IMon.type) :
  isIAlg (hom A B) := imfunQ_isIAlg A B.

Check IMon.type : IAlg_enriched_quiver.type.

(*********************************************************)
(*
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

Definition icmfunQ_zero {A B: ICMon.type} : hom A B := fun a : A => munit.

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
refine (massoc _ _ _).
Qed.
Obligation 2.
unfold left_id, mop; simpl; intros.
unfold icmfunQ_comp, icmfunQ_zero; simpl; intros.
eapply functional_extensionality; intro x0.
refine (mlid _).
Qed.
Obligation 3.
unfold right_id, mop; simpl; intros.
unfold icmfunQ_comp, icmfunQ_zero; simpl; intros.
eapply functional_extensionality; intro x0.
refine (mrid _).
Qed.

(* Program Definition icmfunQ_isICAlg (A B: ICMon.type) :
  isICAlg (hom A B) := isICAlg.Build (hom A B) _ _.
Obligation 1.
econstructor.
unfold commutative, mop; simpl; intros.
unfold icmfunQ_comp; simpl; intros.
eapply functional_extensionality; intro x0.
destruct B.
destruct class.
destruct enriched_cat_case1_isICMon_mixin.
simpl in *.
destruct ica0.
destruct isca0.
eapply acomm0; auto.
Qed.
Obligation 2.
econstructor.
unfold idempotent, mop; simpl; intros.
unfold icmfunQ_comp; simpl; intros.
eapply functional_extensionality; intro x0.
destruct B.
destruct class.
destruct enriched_cat_case1_isICMon_mixin.
simpl in *.
destruct ica0.
destruct isia0.
eapply aidem0; auto.
Qed. *)

(* Program Definition icmfunQ_isICMon (A B: ICMon.type) :
  isICMon (hom A B) := isICMon.Build (hom A B) _ _.
Obligation 1.
eapply icmfunQ_isICAlg.
Qed.
Obligation 2.
eapply icmfunQ_isMon.
Qed. *)

HB.instance Definition icmfunQ_isMonoid (A B: ICMon.type) :
  isMon (hom A B) := icmfunQ_isMon A B.

