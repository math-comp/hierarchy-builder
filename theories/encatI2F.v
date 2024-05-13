Require Import ssreflect ssrfun.
Unset Universe Checking.
From HB Require Import structures cat encatP encatD encatI.
Set Universe Checking.
Require Import Coq.Program.Equality FunctionalExtensionality.

Obligation Tactic := done || idtac.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Add Search Blacklist "__canonical__".

Local Open Scope algebra_scope.

Local Open Scope cat_scope.

(*
Notation "'sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'sigma'  '/ ' x .. y ,  '/ ' p ']'")
  : type_scope.
*)

(************************************************************************)

(** DEFINITION OF DOUBLE CATEGORY (based on internal category) *)

(* A double category is an internal category in cat
   - The objects are the objects of C0
   - The vertical maps are the maps of C0
   - The horizontal maps are the objects of C1
   - The 2-cells are the maps of C1

  About identities:
  - The identity vertical map on (x : C) is \idmap_x
  - The identity horizontal map on (x : C) is iid x
  - the identity 2-cell on (x : C) is iid (\idmap_x) = \idmap_(iid x)

  About compositions:
   - The vertical composition of maps is the composition of C0
   - The vertical compositions of 2-cells is the composition of C1
     (and it agrees with the former because src and tgt are functors
      and because iid is a iHom-map)
   - The horizontal composition of maps is the object part of icomp
   - The horizontal composition of 2-cells is the map part of icomp
 *)

(* basically, the internal category adds the D1 category to the base
D0 category, which is C0 (an object of cat, which is shown to have
pullbacks) *)
Definition doublecat := icat cat.

(* Check (doublecat <~> ???) *)
(* HB.structure' Definition DoubleCat := @InternalCat cat.  *)
(*
Print Assumptions doublecat.
About congr1_funext.
*)

(* XXX HB.tag requires 'icat cat' instead of 'doublecat' *)
Fail HB.tag Definition D0_cat (T: doublecat) : cat := @InternalCat.sort cat T.

(* probably this tag is not needed, anyway *)
HB.tag Definition D0_cat (T: icat cat) : cat := @InternalCat.sort cat T.

HB.tag Definition D1_cat (T: icat cat) : cat := @C1 cat T.

Definition D0_iHom (T: icat cat) : iHom (D0_cat T).
  econstructor; eauto.
  instantiate (1:= D0_cat T).
  econstructor; eauto.
  econstructor; eauto.
  exact idmap.
  exact idmap.
Defined.  
 
Definition D1_iHom (T: icat cat) : iHom (D0_cat T).
  econstructor; eauto.
  instantiate (1:= @C1 cat T).
  econstructor; eauto.
  econstructor; eauto.
  exact src.
  exact tgt.
Defined.  
  
Definition C0_IntQuiv' (X: doublecat) : InternalQuiver.type cat.
  Fail have xx: InternalQuiver.type cat := HB.pack X.
  destruct X.
  destruct class as [K1 K2 K3 K4].
  econstructor; eauto.
  instantiate (1:=sort).
  econstructor; eauto.
Defined.

(* HB.tag *)
Definition C0_IntQuiv (X: icat cat) : InternalQuiver.type cat :=
  C0_IntQuiv' X.

Definition C0_IntPCat' (X: doublecat) : InternalPreCat.type cat.
  Fail have xx: InternalPreCat.type cat := HB.pack X.
  destruct X.
  destruct class as [K1 K2 K3 K4].
  econstructor; eauto.
  instantiate (1:=sort).
  econstructor; eauto.
Defined.

(* HB.tag *)
Definition C0_IntPCat (X: icat cat) : InternalPreCat.type cat :=
  C0_IntPCat' X.  

Definition dcHsource' (T: doublecat) :
  Functor.type (D1_cat T) (D0_cat T).
 destruct T.    
 destruct class as [K1 K2 K3 K4].
 simpl; simpl in *.
 destruct K1; simpl in *; simpl.   
 destruct K2 as [[[src0 tgt0]]];
 simpl in *; simpl.   
 eapply src0.
Defined.

(* HB.tag *)
Definition dcHsource (T: icat cat) : Functor.type (D1_cat T) (D0_cat T) :=
  dcHsource' T.  

Lemma dcHtarget' (T: doublecat) :
  Functor.type (D1_cat T) (D0_cat T).
 destruct T.    
 destruct class as [K1 K2 K3 K4].
 simpl; simpl in *.
 destruct K1; simpl in *; simpl.   
 destruct K2 as [[[src0 tgt0]]];
 simpl in *; simpl.   
 eapply tgt0.
Defined.

(* HB.tag *)
Definition dcHtarget (T: icat cat) : Functor.type (D1_cat T) (D0_cat T) :=
  dcHtarget' T.  

Definition dcHunit' (T: doublecat) :
  Functor.type (D0_cat T) (D1_cat T).
 destruct T.    
 destruct class as [K1 K2 K3 K4].
 simpl; simpl in *.
 destruct K1; simpl in *; simpl.
 destruct K3.
 eapply iidI.  
Defined.

(* HB.tag *)
Definition dcHunit (T: icat cat) :
  Functor.type (D0_cat T) (D1_cat T) := dcHunit' T.

Definition ptype_cat (T: doublecat) : cat.
  pose v := (commaE.pcomma_cat (dcHtarget T) (dcHsource T)).
  econstructor; eauto.
  instantiate (1:= commaE.ptype (dcHtarget T) (dcHsource T)).
  econstructor; eauto.
Defined.  

Definition dcHcompP (T: doublecat) : ptype_cat T ~> D1_cat T.
  destruct T.    
  destruct class as [K1 K2 K3 K4].
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  simpl in *; simpl.
  exact icompI.
Defined.

Definition dcHcompP_left (T: doublecat) : ptype_cat T ~> D1_cat T.
  set (pp := iprod_pb (@C1 cat T) (@C1 cat T)).
  set (f := bot2left pp).
  destruct T.    
  destruct class as [K1 K2 K3 K4].
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  simpl in *; simpl.
  eapply f.
Defined.

Definition dcHcompP_right (T: doublecat) : ptype_cat T ~> D1_cat T.
  set (pp := iprod_pb (@C1 cat T) (@C1 cat T)).
  set (f := bot2right pp).
  destruct T.    
  destruct class as [K1 K2 K3 K4].
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  simpl in *; simpl.
  eapply f.
Defined.


(***********************************************************************)

(* 
Definition dcHcomp' (T: doublecat) :
  Functor.type ((D1_iHom T) *_(D0_cat T) (D1_iHom T)) (D1_cat T).

Definition dcHcomp' (T: doublecat) :
  Functor.type ((@C1 cat T) *_(D0_cat T) (@C1 cat T)) (@C1 cat T).
*)

Definition dcHcomp' (T: doublecat) :
    ((@C1 cat T) *_(D0_cat T) (@C1 cat T)) ~> (@C1 cat T).
  destruct T.    
  destruct class as [K1 K2 K3 K4].
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  simpl in *; simpl.
  exact icompI.
Defined.

(* make type difference more explicit *)
Definition dcHcomp'' (T: doublecat) :
    ((D1_iHom T) *_(D0_cat T) (D1_iHom T)) ~> (D1_cat T).
  destruct T.    
  destruct class as [K1 K2 K3 K4].
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  simpl in *; simpl.
  exact icompI.
Defined.
 
(* HB.tag *)
Definition dcHcomp (T: icat cat) :
  Functor.type ((D1_iHom T) *_(D0_cat T) (D1_iHom T)) (D1_cat T) :=
  dcHcomp'' T.

Definition dcHcomp_left (T: doublecat) :
  ((D1_iHom T) *_(D0_cat T) (D1_iHom T)) ~> (D1_cat T). 
  unfold hom; simpl.
  set (pp := iprod_pb (@C1 cat T) (@C1 cat T)).
  set (f := bot2left pp).
  eapply f.
Defined.

Definition dcHcomp_right (T: doublecat) :
  ((D1_iHom T) *_(D0_cat T) (D1_iHom T)) ~> (D1_cat T). 
  unfold hom; simpl.
  set (pp := iprod_pb (@C1 cat T) (@C1 cat T)).
  set (f := bot2right pp).
  eapply f.
Defined.

(***********************************************************************)

Lemma dcHunit_src (T: icat cat) :  
   (dcHunit T) \; (dcHsource T) = idmap. 
Admitted. 

Lemma dcHunit_tgt (T: icat cat) :  
   (dcHunit T) \; (dcHtarget T) = idmap. 
Admitted. 

Lemma dcHcompP_src (T: icat cat) :  
    (dcHcompP T) \; (dcHsource T) = (dcHcompP_left T) \; (dcHsource T). 
Admitted. 

Lemma dcHcompP_tgt (T: icat cat) :  
    (dcHcompP T) \; (dcHtarget T) = (dcHcompP_right T) \; (dcHtarget T). 
Admitted. 

Lemma dcHcomp_src (T: icat cat) :  
    (dcHcomp T) \; (dcHsource T) = (dcHcomp_left T) \; (dcHsource T). 
Admitted. 

Lemma dcHcomp_tgt (T: icat cat) :  
    (dcHcomp T) \; (dcHtarget T) = (dcHcomp_right T) \; (dcHtarget T). 
Admitted. 


(***********************************************************************)

Lemma dcHunit_o_src (T: icat cat) :  
   forall a: D0_cat T, dcHsource T (dcHunit T a) = a. 
Admitted. 
  
Lemma dcHunit_f_src (T: icat cat) :  
  forall (a b: D0_cat T) (m: a ~> b),
    dcHsource T <$> (dcHunit T <$> m) ~= m. 
Admitted.
  
Lemma dcHunit_o_tgt (T: icat cat) :  
   forall a: D0_cat T, dcHtarget T (dcHunit T a) = a. 
Admitted. 
  
Lemma dcHunit_f_tgt (T: icat cat) :  
  forall (a b: D0_cat T) (m: a ~> b),
    dcHtarget T <$> (dcHunit T <$> m) ~= m. 
Admitted.

Lemma dcHcomp_o_src (T: icat cat) :  
  forall (a: D1_iHom T *_(D0_cat T) D1_iHom T),
    dcHsource T (dcHcomp T a) = dcHsource T (dcHcomp_left T a). 
Admitted. 

Lemma dcHcomp_f_src (T: icat cat) :  
  forall (a b: D1_iHom T *_(D0_cat T) D1_iHom T) (m: a ~> b),
    dcHsource T <$> (dcHcomp T <$> m) ~=
      dcHsource T <$> (dcHcomp_left T <$> m). 
Admitted. 

Lemma dcHcomp_o_tgt (T: icat cat) :  
  forall (a: D1_iHom T *_(D0_cat T) D1_iHom T),
    dcHtarget T (dcHcomp T a) = dcHtarget T (dcHcomp_right T a). 
Admitted. 

Lemma dcHcomp_f_tgt (T: icat cat) :  
  forall (a b: D1_iHom T *_(D0_cat T) D1_iHom T) (m: a ~> b),
    dcHtarget T <$> (dcHcomp T <$> m) ~=
      dcHtarget T <$> (dcHcomp_right T <$> m). 
Admitted. 

(*********************************************************************)


Definition dcInternalHomT (T: doublecat) : InternalHom.type (D0_cat T).
  unfold D0_cat; simpl.
  destruct T.
  destruct class as [K1 K2 K3 K4].
  destruct K2.
  econstructor; eauto.
Defined.
  
Definition dcInternalHom (T: doublecat) :
  @InternalHom cat (D0_cat T) (D1_cat T). 
  destruct T.
  unfold D0_cat, D1_cat; simpl.
  destruct class as [K1 K2 K3 K4].
  destruct K1.
  simpl; simpl in *.
  destruct K2.
  auto.
Defined.  

Lemma dcInternalHom_eq (T: doublecat) :
  InternalHom.sort (dcInternalHomT T) = D1_cat T.
  unfold dcInternalHomT; simpl.
  destruct T; simpl.
  destruct class as [K1 K2 K3 K4]; simpl.
  destruct K1.
  destruct K2; simpl.
  auto.
Qed.

Lemma dcHsource_eq (T: doublecat) :
  (@src _ _ (dcInternalHomT T)) ~= (dcHsource T).    
  destruct T; simpl.
  destruct class as [K1 K2 K3 K4]; simpl.
  destruct K1 as [H0].
  destruct K2 as [H1] ; simpl.
  destruct H1 as [H1]; simpl.
  destruct H1.
  auto.
Qed.  

Lemma dcHtarget_eq (T: doublecat) :
  (@tgt _ _ (dcInternalHomT T)) ~= (dcHtarget T).    
  destruct T; simpl.
  destruct class as [K1 K2 K3 K4]; simpl.
  destruct K1 as [H0].
  destruct K2 as [H1] ; simpl.
  destruct H1 as [H1]; simpl.
  destruct H1.
  auto.
Qed.  

(*********************************************************************)

(* lift to internal morphisms for D1 *)
Definition iHom_lift (T: doublecat) : iHom (D0_cat T).
  unfold D0_cat, D1_cat in *; simpl in *; simpl.
  destruct T.
  destruct class as [K1 K2 K3 K4]; simpl in *; simpl.
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  econstructor; eauto.
  instantiate (1:= C2).
  econstructor; eauto.
  econstructor.
  exact src.
  exact tgt.
Defined.  

(* lift to internal morphisms for D0 *)
Definition iHom0_lift (T: doublecat) : iHom (D0_cat T).
  unfold D0_cat, D1_cat in *; simpl in *; simpl.
  destruct T.
  destruct class as [K1 K2 K3 K4]; simpl in *; simpl.
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  econstructor; eauto.
  instantiate (1:= sort).
  econstructor; eauto.
  econstructor.
  exact idmap.
  exact idmap.
Defined.  


(********************************************************************)

Definition mk_prod_span (T: doublecat) :
  span ((@iHom_lift T) :> cat) ((@iHom_lift T) :> cat) :=
  iprod_pb (@iHom_lift T) (@iHom_lift T).

Definition iHom_prod_lift (T: doublecat) : iHom (D0_cat T).
  set x1 := iHom_lift T.
  set y1 := iHom_lift T.
  set pp := iprod_pb x1 y1.
  set il := iprodl x1 y1.
  set ir := iprodr x1 y1.
  econstructor.
  instantiate (1 := x1 *_(D0_cat T) y1).
  econstructor; eauto.
  econstructor; eauto.
  { destruct x1.
    destruct class as [K]; simpl in *; simpl.
    destruct K.
    exact (il \; src).
  }  
  { destruct y1.
    destruct class as [K]; simpl in *; simpl.
    destruct K.
    exact (ir \; tgt).
  }  
Defined.  

Definition iHom_prod_liftE (T: doublecat) (x y: iHom (D0_cat T))
  (s: span (x :> cat) (y :> cat)) : iHom (D0_cat T).
  set src1 := @src _ _ x.
  set tgt2 := @tgt _ _ y.
  simpl in *.
  destruct T; simpl in *.
  destruct s; simpl in *.
  exists bot.
  econstructor; eauto.
  econstructor; eauto.
  exact (bot2left \; src1).
  exact (bot2right \; tgt2).
Defined.

Definition iHom_prod_liftD (T: doublecat) (x y: iHom (D0_cat T)) :
  iHom (D0_cat T).
  set bb := @iprod_pb cat (D0_cat T) x y.
  set ff := @iHom_prod_liftE T x y.
  destruct T; simpl in *.
  specialize (ff bb); eauto.
Defined.

Definition iHom_prod_liftF (T: doublecat) (x y: iHom (D0_cat T)) :
  iHom (D0_cat T).
  set pp := iprod x y.
  set il := iprodl x y.
  set ir := iprodr x y.
  set src1 := @src _ _ x.
  set tgt2 := @tgt _ _ y.
  unfold iprodl, iprodr, iprod in *.
  move: ir il pp.
  set bb := iprod_pb x y.
  simpl in *.
  intros.
  unfold iprod_pb in *.
  unfold pbk in *.
  simpl in *.
  exists (@bot _ _ _ bb).
  econstructor; eauto.
  destruct T; simpl in *.
  econstructor; eauto.
  exact (il \; src1).
  exact (ir \; tgt2).
Defined.  


(**********************************************************************)

(*** definition of horizontal homset (corresponds to hhom) *)
(* HB.tag *)
Definition dcHhom (T: icat cat) :
  transpose (D0_cat T) -> transpose (D0_cat T) -> U :=
  fun x y =>
    sigma (h: D1_cat T), dcHsource T h = x /\ dcHtarget T h = y.      

Definition dcHhom_impl1 (T: doublecat) :
  (sigma x y, @dcHhom T x y) -> (D1_cat T).
  unfold D1_cat, dcHhom.
  destruct T.
  simpl.
  destruct class as [K1 K2 K3 K4]; simpl.
  destruct K1 as [H0].
  destruct K2 as [H1] ; simpl.
  destruct H1 as [H1]; simpl.
  destruct H1; simpl.
  destruct K3; simpl.
  destruct K4; simpl.
  simpl in *.
  intro.
  destruct X as [x [y [h X]]].
  exact h.
Defined.

Definition dcHhom_impl2 (T: doublecat) :
  (D1_cat T) -> (sigma x y, @dcHhom T x y).
  unfold D1_cat, dcHhom.
  destruct T.
  simpl.
  destruct class as [K1 K2 K3 K4]; simpl.
  destruct K1 as [C2].
  destruct K2 as [H1] ; simpl.
  destruct H1 as [H1]; simpl.
  destruct H1; simpl.
  destruct K3; simpl.
  destruct K4; simpl.
  simpl in *.
  
  intro.
  exists (src X).
  exists (tgt X).
  exists X.
  auto.
Defined.  
  
Lemma dcHhom_iso1 (T: doublecat) (x: D1_cat T) :
   dcHhom_impl1 (dcHhom_impl2 x) = x.
  unfold dcHhom_impl1, dcHhom_impl2; simpl.
  unfold D1_cat in *; simpl; simpl in *.
  destruct T.
  destruct class as [K1 K2 K3 K4]; simpl in *; simpl.
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  auto. 
Qed.   
   
Lemma dcHhom_iso2 (T: doublecat) (x: sigma x y, @dcHhom T x y) :
   dcHhom_impl2 (dcHhom_impl1 x) = x.
  unfold dcHhom_impl1, dcHhom_impl2; simpl.
  destruct x as [x [y [h [X1 X2]]]].
  unfold D1_cat in *; simpl; simpl in *.
  unfold D0_cat in *; simpl; simpl in *.
  destruct T.
  destruct class as [K1 K2 K3 K4]; simpl in *; simpl.
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  inversion X1; subst.
  auto.
Qed.

Definition D1_morph_liftA (T: doublecat) (a b: transpose (D0_cat T)) 
   (h1: dcHhom a b) : D1_cat T.
  eapply (@dcHhom_impl1 T). 
  destruct T; simpl in *.
  exists a.
  exists b.
  exact h1.
Defined.

Definition mk_ptype_auxA (T: doublecat) (a b c: transpose (D0_cat T))
                   (h1: dcHhom a b) (h2: dcHhom b c) :
  commaE.ptype (@tgt cat (D0_cat T) (iHom_lift T)) 
               (@src cat (D0_cat T) (iHom_lift T)). 
  unfold commaE.ptype.
  
  have @hh1: D1_cat T := D1_morph_liftA h1.
  have @hh2: D1_cat T := D1_morph_liftA h2.
  
  destruct T; simpl in *.
  destruct class as [K1 K2 K3 K4]; simpl in *; simpl.
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  simpl in *; simpl.

  exists (hh1, hh2).
  subst hh1 hh2.
  simpl; simpl in *.
    
  destruct h1 as [h1 [p1 q1]]; simpl in *; simpl.
  destruct h2 as [h2 [p2 q2]]; simpl in *; simpl.
  rewrite q1.
  rewrite p2.
  auto.
Defined.  

Definition mk_prod_auxA (T: doublecat) (a b c: transpose (D0_cat T))
                   (h1: dcHhom a b) (h2: dcHhom b c) :
  (iHom_lift T) *_(D0_cat T) (iHom_lift T).
  eapply (@mk_ptype_auxA T a b c); eauto.
Defined.  


(*********************************************************************)

(* tag probably not need, but definition is *)
HB.tag Definition transpose_D0 (T: icat cat) : cat :=
  transpose (D0_cat T).
#[wrapper] HB.mixin Record IsDCH0Quiver (T: icat cat) := {
    is_hquiver : IsQuiver (transpose_D0 T)
}.
(* vertical and horizontal quivers, defining cells.
   non-forgetful inheritace warning  *)
Unset Universe Checking.
#[short(type="dch0quiver")]
HB.structure Definition DCH0Quiver : Set :=
  { C of IsDCH0Quiver C }.
Set Universe Checking.

Unset Universe Checking. 
Definition dcH0QuiverD (T: icat cat) :
  IsQuiver (transpose_D0 T) :=
  IsQuiver.Build (transpose (D0_cat T)) (@dcHhom T).  
Set Universe Checking.

(* XXX does not like the composed lifter *)
Fail HB.instance Definition dcH0Quiver (T: icat cat) :
  IsQuiver (transpose (D0_cat T)) := dcH0QuiverD T.

(* XXX non-forgetful inheritance warning, unclear.
    IsH0Quiver (D0_cat T) should follow by wrapping *)
HB.instance Definition dcH0Quiver (T: icat cat) :
  IsQuiver (transpose_D0 T) := dcH0QuiverD T.

Definition dcHD0QuiverD (T: doublecat) : HD0Quiver (D0_cat T).
  set X := dcH0QuiverD T.
  destruct T.
  econstructor; eauto.
  instantiate (1:=X).   (* wrapped instance *)
  econstructor; eauto.
Defined.

(* XXX non-forgetful inheritance warning, expected as this should be
   automatically derived by wrapping dcH0Quiver and the fact that
   D0_cat is a cat, hence a quiver *)
HB.instance Definition dcHD0QuiverT (T: doublecat) : HD0Quiver (D0_cat T) :=
  dcHD0QuiverD T.

(* XXX there should be no need for this. added to patch up types
   further down, due to a failure to detect dcHD0QuiverT *)
Definition dcHD0Quiver (T: doublecat) : HD0Quiver.type.
  set X := dcH0QuiverD T.
  destruct T.
  econstructor; eauto.
  instantiate (1:=sort).
  econstructor; eauto.
  instantiate (1:=X).
  econstructor; eauto.
Defined.

(************************************************************************)

Definition D1_morph_lift (T: doublecat) (a b: dcHD0Quiver T) 
  (h1: a +> b) : D1_cat T.
  destruct T.
  unfold hhom in h1.
  unfold hom in *; simpl in *.
  eapply D1_morph_liftA; eauto.
Defined.

Definition mk_ptype_aux (T: doublecat) (a b c: dcHD0Quiver T)
                   (h1: a +> b) (h2: b +> c) :
  commaE.ptype (@tgt cat (D0_cat T) (iHom_lift T))
               (@src cat (D0_cat T) (iHom_lift T)).
  unfold commaE.ptype. 

  have @hh1: D1_cat T := D1_morph_lift h1.
  have @hh2: D1_cat T := D1_morph_lift h2.

  destruct T; simpl in *.
  destruct class as [K1 K2 K3 K4]; simpl in *; simpl.
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  simpl in *; simpl.

  exists (hh1, hh2).
  subst hh1 hh2.
  simpl; simpl in *.
    
  destruct h1 as [h1 [p1 q1]]; simpl in *; simpl.
  destruct h2 as [h2 [p2 q2]]; simpl in *; simpl.
  rewrite q1.
  rewrite p2.
  auto.
Defined.  

Definition mk_prod_aux (T: doublecat) (a b c: dcHD0Quiver T)
  (h1: a +> b) (h2: b +> c) :
  (iHom_lift T) *_(D0_cat T) (iHom_lift T).
  eapply (@mk_ptype_aux T a b c h1 h2); eauto.
Defined.  

(**********************************************************************)

(*
(*** definition of horizontal homset (corresponds to hhom) *)
(* HB.tag *)
Definition dcHcomp1 (T: icat cat) :
  D1_cat T -> D1_cat T -> U :=
  fun h1 h2 => dcHsource T h1 = dcHtarget T h2.      

Program Definition ipairCC (T: icat cat) (C0: cat) {x0 x1 x2 x3 : iHom C0}
  (f : x0 ~>_(iHom C0) x2) (g : x1 ~> x3) : (x0 *_C0 x1) ~> (x2 *_C0 x3).
  set em := ipairC f g.
  exact em.
Defined.


(* lift to internal morphisms for D1 *)
Definition iHom_lift' (T: doublecat) : iHom (D0_cat T).
  unfold D0_cat, D1_cat in *; simpl in *; simpl.
  destruct T.
  destruct class as [K1 K2 K3 K4]; simpl in *; simpl.
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  econstructor; eauto.
  instantiate (1:= C2).
  econstructor; eauto.
  econstructor.
  exact src.
  exact tgt.
Defined.  


(* make type difference more explicit *)
Definition dcHcompI (T: doublecat) :
  ((D1_iHom T) *_(D0_cat T) (D1_iHom T)) ~>_(iHom_lift T) (D1_iHom T).
  
  destruct T.    
  destruct class as [K1 K2 K3 K4].
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  simpl in *; simpl.
  exact icompI.
Defined.
*)

Definition dcHcompI' (T: doublecat) :
  pbC0 (@C1 cat T) (@C1 cat T) ~>_(iHom T) (iHom_lift T).
  destruct T.
  destruct class as [K1 K2 K3 K4]; simpl in *; simpl.
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  eapply icompI.
Defined.  

Definition dcHcompI (T: doublecat) :
(*  pbC0 (iHom_lift T) (iHom_lift T) ~>_(iHom T) (iHom_lift T). *)
  ((iHom_lift T) *_(D0_cat T) (iHom_lift T) : iHom T) ~>_(iHom T)
    (iHom_lift T).
  destruct T.
  destruct class as [K1 K2 K3 K4]; simpl in *; simpl.
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  eapply icompI.
Defined.  

Definition dcHunitI (T: doublecat) :
 (iHom0_lift T) ~>_(iHom T) (iHom_lift T).
  destruct T.    
  destruct class as [K1 K2 K3 K4].
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  eapply iidI.  
Defined.

Definition Cmorph {C: prepbcat} (C0 : C)
     (x y : @iHom C C0) (m: x ~>_(@iHom C C0) y) : (x :> C) ~>_C (y :> C).
  destruct m as [m P].
  exact m.
Defined.  

Definition dcIpairI (T: icat cat) {x0 x1 x2 x3 : iHom T}  
  (f : x0 ~>_(iHom T) x2) (g : x1 ~>_(iHom T) x3) : 
(*    (pbC0 x0 x1) ~>_(iHom T) (pbC0 x2 x3). *)
    (x0 *_(D0_cat T) x1 : iHom T) ~>_(iHom T) (x2 *_(D0_cat T) x3 : iHom T).
eapply (@ipairI cat); eauto.
Defined.

Definition dcIprodIAsc (T: icat cat) (c1 c2 c3 : iHom T) :   
(*   ((pbC0 (pbC0 c1 c2) c3)) ~>_(iHom T) (pbC0 c1 (pbC0 c2 c3)).  *)
  (((c1 *_(D0_cat T) c2 : iHom T) *_(D0_cat T) c3) : iHom T) ~>_(iHom T)
    (c1 *_(D0_cat T) (c2 *_(D0_cat T) c3 : iHom T) : iHom T).  
eapply (@iprodIAsc cat).             
Defined.

Definition icompA1_def (T: icat cat) :=    
  (dcIpairI (dcHcompI T) (@idmap (iHom T) (iHom_lift T))
     \; dcHcompI T) = 
    dcIprodIAsc _ _ _
      \; (dcIpairI (@idmap (iHom T) (iHom_lift T)) (dcHcompI T))
      \; dcHcompI T.

Definition icomp1l_def (T: icat cat) :=          
  Cmorph (dcIpairI (@idmap (iHom T) (iHom_lift T)) (dcHunitI T) \;
            (dcHcompI T))
  = @iprodl cat (D0_cat T) (iHom_lift T) (iHom0_lift T). 

Definition icomp1r_def (T: icat cat) :=          
  Cmorph (dcIpairI (dcHunitI T) (@idmap (iHom T) (iHom_lift T)) \;
            (dcHcompI T))
  = @iprodr cat (D0_cat T) (iHom0_lift T) (iHom_lift T). 


(*************************************************************************)
(* flatter def of internal cat (for cat), consistently using HB *)

Definition Cat_pair : Type := (cat * cat)%type.

HB.mixin Record isIBase (T: Cat_pair) := { 
  dHSource (X: cat) : X ~> (fst T) ;  
  dHTarget (X: cat) : X ~> (fst T) ; 

  dHSource0 : dHSource (fst T) = @idmap cat (fst T) ;
  dHTarget0 : dHTarget (fst T) = @idmap cat (fst T) ; 
}.
HB.structure Definition IBase :=
  { C of isIBase C }.

HB.mixin Record isPBase T of IBase T := { 
  CCProd (X Y: cat) : cat ;
  dprodl (X Y: cat) : CCProd X Y ~> X ;    
  dprodr (X Y: cat) : CCProd X Y ~> Y ;  

  mkprod (X Y: cat) : X -> Y -> CCProd X Y ; 

  mkprod1 (X Y: cat) (h: X) (k: Y) : @dprodl X Y (@mkprod X Y h k) = h ;   
  mkprod2 (X Y: cat) (h: X) (k: Y) : @dprodr X Y (@mkprod X Y h k) = k ;   
    
  dHSourceP (X Y: cat) :
    dHSource (CCProd X Y) = dprodl X Y \; @dHSource T X ; 
  dHTargetP (X Y: cat) :
    dHTarget (CCProd X Y) = dprodr X Y \; @dHTarget T Y ;    
}.
HB.structure Definition PBase :=
  { C of isPBase C }.

HB.mixin Record isICC T of PBase T := {   
  dIid : (fst T) ~> (snd T) ;  
  dIcomp : @CCProd T (snd T) (snd T) ~> snd T ;  

  dPair (X0 X1 X2 X3: cat) (f: X0 ~> X2) (g: X1 ~> X3) :
    (@CCProd T X0 X1) ~> (@CCProd T X2 X3) ; 

  dIAsc (C1 C2 C3: cat) :
    (@CCProd T (@CCProd T C1 C2) C3) ~>
      (@CCProd T C1 (@CCProd T C2 C3)) ;  

  dIidS : dIid \; @dHSource T (snd T) = @dHSource T (fst T) ;
  dIidT : dIid \; @dHTarget T (snd T) = @dHTarget T (fst T) ;

  dIcompS : dIcomp \; @dHSource T (snd T) =
                @dHSource T (@CCProd T (snd T) (snd T)) ;
  dIcompT : dIcomp \; @dHTarget T (snd T) =
                @dHTarget T (@CCProd T (snd T) (snd T)) ;
    
  dPairS (X0 X1 X2 X3: cat) (f: X0 ~> X2) (g: X1 ~> X3) :
    dPair _ _ _ _ f g \; @dHSource T (@CCProd T X2 X3) =
      dprodl X0 X1 \; @dHSource T X0 ; 

  dPairT (X0 X1 X2 X3: cat) (f: X0 ~> X2) (g: X1 ~> X3) :
    dPair _ _ _ _ f g \; @dHTarget T (@CCProd T X2 X3) =
      dprodr X0 X1 \; @dHTarget T X1 ; 
   
  d_icompA :
    (dPair _ _ _ _ dIcomp (@idmap cat (snd T))) \; dIcomp =
      dIAsc _ _ _ \;
        (dPair _ _ _ _ (@idmap cat (snd T)) dIcomp) \; dIcomp ; 

  d_compL :
     dPair _ _ _ _ (@idmap cat (snd T)) dIid \; dIcomp =
        dprodl (snd T) (fst T) ; 

  d_compR :
     dPair _ _ _ _ dIid (@idmap cat (snd T)) \; dIcomp =
      dprodr (fst T) (snd T)                    
}.
HB.structure Definition ICC := { C of isICC C }.

(********************************************************************)

Definition dHhom (T: ICC.type) :
  transpose (fst (ICC.sort T)) -> transpose (fst (ICC.sort T)) -> U :=
  fun x y =>
    sigma (h: snd (ICC.sort T)),
          @dHSource T (snd (ICC.sort T)) h = x
          /\ @dHTarget T (snd (ICC.sort T)) h = y.      

HB.tag Definition h_D0 (T: ICC.type) : cat :=
  transpose (fst (ICC.sort T)).
#[wrapper] HB.mixin Record IsDH0Quiver C of ICC C := {
    is_hquiver : IsQuiver (h_D0 C)
}.
(* vertical and horizontal quivers, defining cells.
   non-forgetful inheritace warning  *)
Unset Universe Checking.
#[short(type="dh0quiver")]
HB.structure Definition DH0Quiver : Set :=
  { C of IsDH0Quiver C }.
Set Universe Checking.

Definition ddHhom (T: ICC.type) :
  h_D0 T -> h_D0 T -> U :=
  fun x y =>
    sigma (h: snd (ICC.sort T)),
          @dHSource T (snd (ICC.sort T)) h = x
          /\ @dHTarget T (snd (ICC.sort T)) h = y.      

(* non-forgetful inheritace warning  *)
Unset Universe Checking.
HB.instance Definition DH0Quiver_inst (T: ICC.type) :
  IsQuiver (h_D0 T) := @IsQuiver.Build (h_D0 T) (@ddHhom T).
Set Universe Checking.

Unset Universe Checking.
HB.tag Definition dhhom (T : ICC.type) : h_D0 T -> h_D0 T -> U :=
  @hom (h_D0 T).
Set Universe Checking.
Notation "a h> b" := (dhhom a b)
   (at level 99, b at level 200, format "a  h>  b") : cat_scope.

Definition DH0_cat_id (T: ICC.type)
  (a: transpose (fst (ICC.sort T))) : dHhom a a.
  pose src1 := @dHSource T.
  pose tgt1 := @dHTarget T.
  pose iid := @dIid T.
  simpl in *.  
  unfold dHhom; simpl.
  exists (iid a).

  split.
  { assert (@dHSource T (snd (ICC.sort T)) (iid a) =
            (iid \; dHSource (snd (ICC.sort T))) a) as H.
    { auto. }

    rewrite H.
    rewrite dIidS.
    rewrite dHSource0.
    simpl; auto.
  }
    
  { assert (@dHTarget T (snd (ICC.sort T)) (iid a) =
            (iid \; dHTarget (snd (ICC.sort T))) a) as H.
    { auto. }
  
    rewrite H.
    rewrite dIidT.
    rewrite dHTarget0.
    simpl; auto.
  }
Defined.

Definition DH0_cat_comp (T: ICC.type)
  (a b c: (transpose (fst (ICC.sort T)))) 
  (h1: dHhom a b) (h2: dHhom b c) : dHhom a c.
  unfold dHhom in *.
  simpl in *.
  destruct h1 as [h1 [hs1 ht1]].
  destruct h2 as [h2 [hs2 ht2]].
  pose prd := @mkprod T _ _ h1 h2.
  pose cmp := @dIcomp T.
  pose mm := cmp prd.
  exists mm.

  split.
  { subst mm. 

    assert (@dHSource T (snd (ICC.sort T)) (cmp prd) =
            (cmp \; @dHSource T (snd (ICC.sort T))) prd) as H. 
    { auto. }

    rewrite H.
    subst cmp.
    rewrite dIcompS.
    rewrite dHSourceP.
    simpl.
    subst prd.
    rewrite mkprod1.
    rewrite hs1; auto.
  }.  
    
  { subst mm. 

    assert (@dHTarget T (snd (ICC.sort T)) (cmp prd) =
            (cmp \; @dHTarget T (snd (ICC.sort T))) prd) as H. 
    { auto. }

    rewrite H.
    subst cmp.
    rewrite dIcompT.
    rewrite dHTargetP.
    simpl.
    subst prd.
    rewrite mkprod2.
    rewrite ht2; auto.
  }.  
Defined.     

(* non-forgetful inheritace warning  *)
Unset Universe Checking.
HB.instance Definition DH0PreCatD (T: ICC.type) : IsPreCat (h_D0 T) :=
  @IsPreCat.Build (h_D0 T) (@dHhom T) (@DH0_cat_id T) (@DH0_cat_comp T).
Set Universe Checking.


(*************************************************************************)
(* Problematic: does not parametrize C0 ad C1. *)
(*
HB.mixin Record isDIHom T of PBCat T := {  
  CC0 : T ; 
  CC1 : T ;
  CCProd (X Y: T) : T ;                         
}.

HB.structure Definition DIHom :=
  { C of isDIHom C }.

HB.mixin Record isDCC T of DIHom T := { 
  dHSource (X: T) : X ~> CC0 ;  
  dHTarget (X: T) : X ~> CC0 ;

  dprodl (X Y: T) : CCProd X Y ~> X ;    
  dprodr (X Y: T) : CCProd X Y ~> Y ;    

  dHSource0 : dHSource CC0 = @idmap T CC0 ;
  dHTarget0 : dHTarget CC0 = @idmap T CC0 ;
    
  dHSourceP (X Y: T) : dHSource (CCProd X Y) = dprodl X Y \; dHSource X ; 
  dHTargetP (X Y: T) : dHTarget (CCProd X Y) = dprodr X Y \; dHTarget Y ;    
}.

HB.structure Definition DCC :=
  { C of isDCC C }.

HB.mixin Record isDIC T of DCC T := {   
  dIid : @CC0 T ~> @CC1 T ;  
  dIcomp : CCProd (@CC1 T) (@CC1 T) ~> @CC1 T ;  

  dPair (X0 X1 X2 X3: T) (f: X0 ~> X2) (g: X1 ~> X3) :
    (CCProd X0 X1) ~> (CCProd X2 X3) ; 

  dIAsc (C1 C2 C3: T) :
    (CCProd (CCProd C1 C2) C3) ~> (CCProd C1 (CCProd C2 C3)) ; 

  dPairS (X0 X1 X2 X3: T) (f: X0 ~> X2) (g: X1 ~> X3) :
    dPair _ _ _ _ f g \; dHSource (CCProd X2 X3) =
      dprodl X0 X1 \; dHSource X0 ;

  dPairT (X0 X1 X2 X3: T) (f: X0 ~> X2) (g: X1 ~> X3) :
    dPair _ _ _ _ f g \; dHTarget (CCProd X2 X3) =
      dprodr X0 X1 \; dHTarget X1 ; 
   
  d_icompA :
    (dPair _ _ _ _ dIcomp (@idmap T (@CC1 T))) \; dIcomp =
      dIAsc _ _ _ \;
        (dPair _ _ _ _ (@idmap T (@CC1 T)) dIcomp) \; dIcomp ; 

  d_compL :
     dPair _ _ _ _ (@idmap T (@CC1 T)) dIid \; dIcomp =
        dprodl (@CC1 T) (@CC0 T) ; 
     (* ~= @iprodl cat (fst T) (@dIH1 T) (@dIH0 T) *)

  d_compR :
     dPair _ _ _ _ dIid (@idmap T (@CC1 T)) \; dIcomp =
      dprodr (@CC0 T) (@CC1 T)                    
}.

HB.structure Definition DIC := { C of isDIC C }.

Definition DIHom_cat : isDIHom cat.
Admitted.
HB.instance Definition DIHom_cat' := DIHom_cat.

Definition DCC_cat : isDCC cat.
Admitted.
HB.instance Definition DCC_cat' := DCC_cat.

Definition DIC_cat : isDIC cat.
Admitted.
HB.instance Definition DIC_cat' := DIC_cat.

*)

(*************************************************************************)
(* Not good: relies on iHom *)
(*
Definition CCpair := (cat * cat)%type.

HB.mixin Record isDCC (CC: CCpair) := { 
  dHSource : (snd CC) ~> (fst CC) ;  
  dHTarget : (snd CC) ~> (fst CC) ; 
}.

HB.structure Definition DCC :=
  { C of isDCC C }.

HB.mixin Record isDIHom (T: CCpair) of isDCC T := {  
  dIH0 : iHom (fst T) ; 
  dIH1 : iHom (fst T) ;
  dProd (X Y: iHom (fst T)) : iHom (fst T)                         
}.

HB.structure Definition DIHom :=
  { C of isDIHom C & isDCC C }.

HB.mixin Record isDIC (T: CCpair) of isDCC T & isDIHom T := {    
  IH2cat : iHom (fst T) -> cat ; 
  IH2catM (X Y: iHom (fst T)) (f: X ~> Y) : (IH2cat X) ~> (IH2cat Y) ;
    
  ProdBot (X Y: iHom (fst T)) : cat ;
  dIprodl (X Y: iHom (fst T)) : IH2cat (dProd X Y) ~> IH2cat X ;    
  dIprodr (X Y: iHom (fst T)) : IH2cat (dProd X Y) ~> IH2cat Y ;    

  IH2cat0 : IH2cat (@dIH0 T) = fst T ;  
  IH2cat1 : IH2cat (@dIH1 T) = snd T ; 
  IH2catP (X Y: iHom (fst T)) : IH2cat (dProd X Y) = ProdBot X Y ;
                             (*  @iprod cat (fst T) X Y ; *)
    
  dIid : @dIH0 T ~> @dIH1 T ; 
  dIcomp : dProd (@dIH1 T) (@dIH1 T) ~> @dIH1 T ; 

  dPair (X0 X1 X2 X3: iHom (fst T)) (f: X0 ~> X2) (g: X1 ~> X3) :
    (dProd X0 X1) ~> (dProd X2 X3) ; 

  dIAsc (C1 C2 C3: iHom (fst T)) :
    (dProd (dProd C1 C2) C3) ~> (dProd C1 (dProd C2 C3)) ; 
    
  d_icompA :
    (dPair _ _ _ _ dIcomp (@idmap (iHom (fst T)) (@dIH1 T))) \; dIcomp =
      dIAsc _ _ _ \;
        (dPair _ _ _ _ (@idmap (iHom (fst T)) (@dIH1 T)) dIcomp) \; dIcomp ; 

  d_compL :
    IH2catM _ _
      (dPair _ _ _ _ (@idmap (iHom (fst T)) (@dIH1 T)) dIid \; dIcomp) =
        dIprodl (@dIH1 T) (@dIH0 T) ;  
     (* ~= @iprodl cat (fst T) (@dIH1 T) (@dIH0 T) *)

  d_compR :
    IH2catM _ _
      (dPair _ _ _ _ dIid (@idmap (iHom (fst T)) (@dIH1 T)) \; dIcomp) =
      dIprodr (@dIH0 T) (@dIH1 T)                    
}.

HB.structure Definition DIC := { C of isDIC C }.

Definition dHhom (T: DIC.type) :
  transpose (fst (DIC.sort T)) -> transpose (fst (DIC.sort T)) -> U :=
  fun x y =>
    sigma (h: snd (DIC.sort T)), dHSource h = x /\ dHTarget h = y.      

Unset Universe Checking.
Definition dH0QuiverD (T: DIC.type) :
  IsQuiver (transpose (fst (DIC.sort T))) :=
  IsQuiver.Build _ (@dHhom T).  
Set Universe Checking.

Definition H0_cat_id (T: DIC.type)
  (a: transpose (fst (DIC.sort T))) : dHhom a a.
  pose src1 := @dHSource T.
  pose tgt1 := @dHTarget T.
  pose iid := @dIid T.
  simpl in *.
  
  destruct iid as  [m [[P1 P2]]]; simpl in *.
  unfold dHhom; simpl.

  unfold hom in m; simpl in *.

  exists (m a).
*)

(**************************************************************************)
(* Not good: out of HB *)
(*
Record DIHom := {
  dC0 : cat ;
  dC1 : cat ;  
  dHSource : dC1 ~> dC0 ;  
  dHTarget : dC1 ~> dC0 ; 
  iH := iHom dC0 ;  
  dIH0 : iH ; 
  dIH1 : iH ;
  dProd (X Y: iH) : iH                         
}.

HB.mixin Record isDIC (DH : DIHom) := {
  IH2cat : iH DH -> cat ;
  IH2catM (X Y: iH DH) (f: X ~> Y) : (IH2cat X) ~> (IH2cat Y) ;
  
  dIprodl (X Y: iH DH) : IH2cat (dProd X Y) ~> IH2cat X;    
  dIprodr (X Y: iH DH) : IH2cat (dProd X Y) ~> IH2cat Y;    
  
  dIid : dIH0 DH ~> dIH1 DH ; 
  dIcomp : dProd (dIH1 DH) (dIH1 DH) ~> dIH1 DH ; 

  dPair (X0 X1 X2 X3: iH DH) (f: X0 ~> X2) (g: X1 ~> X3) :
    (dProd X0 X1) ~> (dProd X2 X3) ; 

  dIAsc (C1 C2 C3: iH DH) :
    (dProd (dProd C1 C2) C3) ~> (dProd C1 (dProd C2 C3)) ; 
    
  d_icompA :
    (dPair _ _ _ _ dIcomp (@idmap (iH DH) (dIH1 DH))) \; dIcomp =
      dIAsc _ _ _ \;
        (dPair _ _ _ _ (@idmap (iH DH) (dIH1 DH)) dIcomp) \; dIcomp ;

  d_compL :
    IH2catM _ _
      (dPair _ _ _ _ (@idmap (iH DH) (dIH1 DH)) dIid \; dIcomp) =
        dIprodl (dIH1 DH) (dIH0 DH) ;    
    (* ~= @iprodl cat (dC0 DH) (dIH1 DH) (dIH0 DH) *)

  d_compR :
    IH2catM _ _
      (dPair _ _ _ _ dIid (@idmap (iH DH) (dIH1 DH)) \; dIcomp) =
      dIprodr (dIH0 DH) (dIH1 DH)                    
}.

HB.structure Definition DIC := { C of isDIC C }.

*)
(*
Record IsDDCC (CC: DDCC) := {
  ddC0 := fst CC ;
  ddC1 := snd CC ;  
  ddHSource : ddC1 ~> ddC0 ;  
  ddHTarget : ddC1 ~> ddC0 ; 
  ddIHC0 := @mkIHomI ddC0 ddC0 idmap idmap ;  
  ddIHC1 := mkIHomI ddHSource ddHTarget ; 
}.
*)

(**********************************************************************)

Definition dcHsourceF (T: doublecat) (C: iHom T) :
  Functor.type (C :> cat) (D0_cat T) := @src cat T C.

Definition dcHtargetF (T: doublecat) (C: iHom T) :
  Functor.type (C :> cat) (D0_cat T) := @tgt cat T C.

Definition ipairCC1 (T: icat cat) {x0 x1 x2 x3 : iHom T}  
  (f : (x0 :> cat) ~>_cat (x2 :> cat)) (g : (x1 :> cat) ~>_cat (x3 :> cat)) :
  dcHsourceF x0 = f \; dcHsourceF x2 ->
  dcHsourceF x1 = g \; dcHsourceF x3 ->
  dcHtargetF x0 = f \; dcHtargetF x2 ->
  dcHtargetF x1 = g \; dcHtargetF x3 ->  
  sigma mr: (x0 *_T x1 :> cat) ~>_cat (x2 *_T x3 :> cat),
      iprodl x0 x1 \; f = mr \; iprodl x2 x3 /\
        iprodr x0 x1 \; g = mr \; iprodr x2 x3.
Admitted. 

Program Definition ipairCP (T: icat cat) {x0 x1 x2 x3 : iHom T}
  (f : x0 ~>_(iHom T) x2) (g : x1 ~>_(iHom T) x3) :
  sigma mr: (x0 *_T x1 :> cat) ~>_cat (x2 *_T x3 :> cat),
      iprodl x0 x1 \; f = mr \; iprodl x2 x3 /\
      iprodr x0 x1 \; g = mr \; iprodr x2 x3. 
eapply (@ipairP cat); eauto.
Defined.

Program Definition ipairCC (T: icat cat) {x0 x1 x2 x3 : iHom T}
  (f : x0 ~>_(iHom T) x2) (g : x1 ~>_(iHom T) x3) :
  (x0 *_T x1 :> cat) ~>_cat (x2 *_T x3 :> cat). 
eapply (@ipairC cat); eauto.
Defined.

Program Definition cat2ihom (T: icat cat) (C: cat) (s t: C ~> T) : iHom T.
econstructor; eauto.
instantiate (1:=C).
econstructor; eauto.
econstructor.
exact s.
exact t.
Defined. 

(*
Program Definition ihom2cat (T: icat cat) (C: iHom T) : cat :=
  InternalHom.sort T.
*)
(*
Definition icompA1_def (T: icat cat) :=    
 ( <( dcHcomp T,
      @idmap (D0_iHom T) (D1_cat: D1_iHom T) )> \; dcHcomp T ) =
     ((@iprodIAsc cat (D0_cat T) (D1_cat: D1_iHom T)) _ _) \;
       <<( (@idmap  (D0_iHom T) (D1_cat: D1_iHom T)), dcHcomp T )>> \;
       dcHcomp T.

Definition icompA1_def (T: icat cat) :=    
 (<( (dcHcomp T : ((D1_iHom T *_ (D0_cat T) D1_iHom T :> iHom (D0_cat T)) ~> (D0_cat T)) (D1_cat T)),
     (@idmap (D0_iHom T) (D1_cat: D1_iHom T)) )> \; dcHcomp T) =
     ((@iprodIAsc cat (D0_cat T) (D1_cat: D1_iHom T)) _ _) \;
       <<( (@idmap  (D0_iHom T) (D1_cat: D1_iHom T)), dcHcomp T )>> \;
       dcHcomp T.
*)

(********************************************************************)


(* XXX why?? *)
Fail Definition H0_cat_id (T: icat cat) (a: transpose (D0_cat T)) : a +> a.

(* H0 horizontal identity *)
Definition H0_cat_id (T: icat cat) (a: transpose (D0_cat T)) : dcHhom a a.
  pose src1 := @src cat (D0_cat T) T.
  pose tgt1 := @tgt cat (D0_cat T) T.
  simpl in *.

  unfold hhom.
  unfold hom; simpl.
      
  destruct T; simpl in *.
  destruct class as [K1 K2 K3 K4]; simpl in *; simpl.
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  
  unfold hom in iidI; simpl in *.
  unfold hom in iidI; simpl in *.
    
  destruct iidI as [m class]; simpl in *.
  destruct class as [Q]; simpl in *.
  destruct Q as [p1 p2]; simpl in *.
  
  unfold dcHhom; simpl.

  assert (m \; src = src1) as Es1.
  { auto. }

(*  assert (src1 = idmap) as Es2.
  { auto. } *)
  assert ((m \; src) a = src1 a) as Es3.
  { rewrite Es1; auto. } 
  
  assert (src (m a) = a) as Es4.
  { eauto. }

  assert (m \; tgt = tgt1) as Et1.
  { auto. }
(*  assert (tgt1 = idmap) as Et2.
  { auto. } *)

  assert ((m \; tgt) a = tgt1 a) as Et3.
  { rewrite Et1; auto. }
  
  assert (tgt (m a) = a) as Et4.
  { eauto. }

  exists (m a); eauto.
Defined.  

(* XXX there should be no need for dcHD0Quiver *)
Definition H0_cat_Id (T: doublecat) (a: dcHD0Quiver T) : a +> a.
  destruct T; simpl in *.
  unfold hhom.
  unfold hom; simpl.
  eapply H0_cat_id.
Defined.  

(********************************************************************)


(* XXX why?? *)
Fail Definition H0_cat_comp (T: icat cat) (a b c: transpose_D0 T) 
   (h1: a +> b) (h2: b +> c) : a +> c.

(* XXX H0 horizontal composition *)
Definition H0_cat_comp (T: icat cat) (a b c: transpose (D0_cat T)) 
   (h1: dcHhom a b) (h2: dcHhom b c) : dcHhom a c.
  (*** lifting of h1 and h2 to D1 objects and iHoms *)
  set hh1 := D1_morph_liftA h1.
  set hh2 := D1_morph_liftA h2.

  (* C1 typed as iHom *)
  set CC := iHom_lift T.

  (* source of h1 (from iHom C1) *)
  pose h1_src := @src cat (D0_cat T) CC.
  (* target of h2 (from iHom C1) *)
  pose h2_tgt := @tgt cat (D0_cat T) CC.

  (* projections of the product as span *)
  set il := iprodl CC CC.
  set ir := iprodr CC CC.
  
  (* source and target of the product as span *)
  set prod_src_f := il \; h1_src.
  set prod_tgt_f := ir \; h2_tgt.

  (*** product as ptype *)
  have @xxx := mk_prod_auxA h1 h2. 
  simpl in *.

  (*** horizontal composition (as iHomHom) *) 
  set cmp_ihh := @icompI cat T.
  simpl in *.

  (* composition as functor *)
  destruct cmp_ihh as [cmp_f [[cmp_p1 cmp_p2]]].
  simpl in *.
  
  (* product of C1, from xxx  *)
  have @X : (@C1 cat T *_ T @C1 cat T).
  { unfold iprod.
    unfold iprod_pb.
    simpl.
    destruct T.
    destruct class as [K1 K2 K3 K4]; simpl.
    destruct K1; simpl.
    destruct K2 as [H]; simpl.
    destruct H as [H]; simpl.
    destruct H; simpl.
    destruct K3; simpl.
    destruct K4; simpl.
    simpl in *. 
    exact xxx.
  }
  (* product as a span, from xxx *)
  have @Y : (CC *_ (D0_cat T) CC).
  { unfold iprod.
    unfold iprod_pb.
    simpl.
    exact xxx.
  }

  set cmp_f_src := cmp_f \; src.
  set cmp_f_tgt := cmp_f \; tgt.
  
  (* we need: comp_f \; src  =  prod_src_f *)
  (* the source of the composition object obtained from X, i.e. 
     (composition morphism > source) X 
   equals the source of the product object obtained from Y. i.e. 
     (left projection > source) Y 
   and similarly for target *)
  assert (cmp_f_src X = prod_src_f Y /\
          cmp_f_tgt X = prod_tgt_f Y) as stE.
  { subst cmp_f_src prod_src_f.
    subst cmp_f_tgt prod_tgt_f.
    unfold src, tgt.
    subst h1_src h2_tgt; simpl.
    destruct T.
    destruct class as [K1 K2 K3 K4]; simpl.
    destruct K1; simpl.
    destruct K2 as [H]; simpl.
    destruct H as [H]; simpl.
    destruct H; simpl.
    destruct K3; simpl.
    destruct K4; simpl.
    simpl in *. 
    
    assert (X = Y) as ee.
    { auto. }
    rewrite ee.
    unfold pcat_prj1, pcat_prj2.

    assert (src (cmp_f Y) = (cmp_f \; src) Y) as ee1.
    { auto. }
    assert (tgt (cmp_f Y) = (cmp_f \; tgt) Y) as ee2.
    { auto. }    
    rewrite ee1.
    rewrite ee2.
    rewrite cmp_p1.
    rewrite cmp_p2.
    auto.
  }
  destruct stE as [srcE tgtE].

  destruct T.
  destruct class as [K1 K2 K3 K4]; simpl.
  destruct K1; simpl.
  destruct K2 as [H]; simpl.
  destruct H as [H]; simpl.
  destruct H; simpl.
  destruct K3; simpl.
  destruct K4; simpl.
  simpl in *. 

  unfold hhom.
  unfold hom; simpl; simpl in *.
  unfold dcHhom.
  simpl.

  (* composition object *)
  exists (cmp_f xxx).

  split.
  { rewrite srcE. 
    destruct h1 as [m1 [ma1 mb1]].
    auto.
  }  
  { rewrite tgtE.
    destruct h2 as [m2 [ma2 mb2]].
    auto.
  }  
Defined.

Definition H0_cat_Comp (T: doublecat) (a b c: dcHD0Quiver T)
  (h1: a +> b) (h2: b +> c) : a +> c.
  destruct T.
  unfold hhom in *.
  unfold hom in *; simpl in *.
  eapply H0_cat_comp; eauto.
Defined.  

(********************************************************************)

(*
Definition dcH0PreCatD (T: doublecat) : IsPreCat (transpose (D0_cat T)).
Admitted. 
*)

(* XXX ?? does not see the H0Quiver instance, i.e. does not see the
   quiver on (transpose_D0 T). it simplifies away transpose instead.
   *)
Definition dcH0PreCatD (T: icat cat) :
  IsPreCat (transpose_D0 T).
(*  := IsPreCat.Build (transpose (D0_cat T)) (@H0_cat_id T) (@H0_cat_comp T). *)
(*  unfold transpose_D0. *)
  assert (forall (a: dcHD0Quiver T), a +> a) as A.
  { eapply (@H0_cat_Id T). }
    econstructor; eauto. (* wrongly simplifies tranpose *)
    intros.
    unfold hhom in *.
    destruct T.
    destruct class as [K1 K2 K3 K4]; simpl.
    destruct K1; simpl.
    destruct K2 as [H]; simpl.
    destruct H as [H]; simpl.
    destruct H; simpl.
    destruct K3; simpl.
    destruct K4; simpl.
    simpl in *. 
    unfold hom in *; simpl in *.
    unfold hom; simpl.
    Fail eapply A; eauto.
admit.
admit.
Admitted. 


Fail Definition dcH0PreCatD' (T: icat cat) :
  IsH0PreCat (dcHD0Quiver T).

Fail Definition dcH0PreCatD' (T: icat cat) :
  IsH0PreCat (D0_cat T).

(* non-forgetful inheritance warning *)
HB.instance Definition dcH0PreCat (T: doublecat) :
  IsPreCat (transpose_D0 T) := dcH0PreCatD T.  

Lemma doublecat2stufunctor (T: doublecat) : STUFunctor.type.
  have @D0 : cat := D0_cat T.

  have @D1 : cat := D1_cat T. 
    
  have @SR : Functor.type D1 D0.
  { destruct T.    
    destruct class as [K1 K2 K3 K4].
    subst D0 D1.
    simpl; simpl in *.
    
    destruct K1; simpl in *; simpl.
   
    destruct K2 as [[[src0 tgt0]]];
      simpl in *; simpl.
    
    eapply src0.
  }

  have @TG : Functor.type D1 D0.
  { destruct T.    
    destruct class as [K1 K2 K3 K4].
    subst D0 D1.
    simpl; simpl in *.
    
    destruct K1; simpl in *; simpl.
   
    destruct K2 as [[[src0 tgt0]]];
      simpl in *; simpl.
    
    eapply tgt0.
  }

  have @UN : Functor.type D0 D1.
  { destruct T.    
    destruct class as [K1 K2 K3 K4].
    subst D0 D1.
    simpl; simpl in *.
    
    destruct K1; simpl in *; simpl.

    destruct K3.

    eapply iidI.
  }  

  have @H0PC : IsPreCat (transpose (D0_cat T)).
  { eapply (dcH0PreCatD T). }

(*  
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
*)
(*
  have DD : DDCat (D0_cat T).
  { econstructor; eauto.
    econstructor; eauto.
    
  
  pose XT : STUFunctor.type := HB.pack T D0 D1 SR TG UN H0PC. 
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  
  auto.
*)
Admitted.   


(**********************************************************************)
(* trying to flatten the def of internal categories, using just records *)

Definition mkIHom (c0 c1: cat) (s t: c1 ~> c0) : @isInternalHom cat c0 c1 :=
  @isInternalHom.Build cat c0 c1 s t.
HB.instance Definition mkIHomI (c0 c1: cat) (s t: c1 ~> c0) :=
  mkIHom s t. 

Record DDCC := {
  ddC0 : cat ;
  ddC1 : cat ;  
  ddHSource : ddC1 ~> ddC0 ;  
  ddHTarget : ddC1 ~> ddC0 ; 
}.

Record DDIHom (CC: DDCC) := {
  IH := iHom (ddC0 CC) ;  
  ddIH0 : IH ; 
  ddIH1 : IH ;
  ddProd (X Y: IH) : IH                         
}.

Record DDIC (CC: DDCC) (DH : DDIHom CC) := {
  DIH2cat : IH DH -> cat ;
  DIH2catM (X Y: IH DH) (f: X ~> Y) : (DIH2cat X) ~> (DIH2cat Y) ;
  
  ddIprodl (X Y: IH DH) : DIH2cat (ddProd X Y) ~> DIH2cat X;    
  ddIprodr (X Y: IH DH) : DIH2cat (ddProd X Y) ~> DIH2cat Y;    

  ddIid : ddIH0 DH ~> ddIH1 DH ; 
  ddIcomp : ddProd (ddIH1 DH) (ddIH1 DH) ~> ddIH1 DH ; 

  ddPair (X0 X1 X2 X3: IH DH) (f: X0 ~> X2) (g: X1 ~> X3) :
    (ddProd X0 X1) ~> (ddProd X2 X3) ; 

  ddIAsc (C1 C2 C3: IH DH) :
    (ddProd (ddProd C1 C2) C3) ~> (ddProd C1 (ddProd C2 C3)) ; 
    
  dd_icompA :
    (ddPair ddIcomp (@idmap (IH DH) (ddIH1 DH))) \; ddIcomp =
      ddIAsc _ _ _ \;
        (ddPair (@idmap (IH DH) (ddIH1 DH)) ddIcomp) \; ddIcomp ;

  dd_compL :
    DIH2catM (ddPair (@idmap (IH DH) (ddIH1 DH)) ddIid \; ddIcomp) =
      ddIprodl (ddIH1 DH) (ddIH0 DH) ;    
    (* ~= @iprodl cat (ddC0 CC) (ddIH1 DH) (ddIH0 DH) *)

  dd_compR :
    DIH2catM (ddPair ddIid (@idmap (IH DH) (ddIH1 DH)) \; ddIcomp) =
      ddIprodr (ddIH0 DH) (ddIH1 DH)                    
}.

(**************************************************************************)

(*
Definition mk_prod_span (T: doublecat) (x y: D1_cat T) :
  span ((@iHom_lift T x) :> cat) ((@iHom_lift T y) :> cat) :=
  iprod_pb (@iHom_lift T x) (@iHom_lift T y).

Definition iHom_prod_lift (T: doublecat) (x y: D1_cat T) :
  iHom (D0_cat T).
  set x1 := iHom_lift x.
  set y1 := iHom_lift y.
  set pp := iprod_pb x1 y1.
  set il := iprodl x1 y1.
  set ir := iprodr x1 y1.
  econstructor.
  instantiate (1 := x1 *_(D0_cat T) y1).
  econstructor; eauto.
  econstructor; eauto.
  { destruct x1.
    destruct class as [K]; simpl in *; simpl.
    destruct K.
    exact (il \; src).
  }  
  { destruct y1.
    destruct class as [K]; simpl in *; simpl.
    destruct K.
    exact (ir \; tgt).
  }  
Defined.  

Definition D1_morph_liftA (T: doublecat) (a b: transpose (D0_cat T)) 
   (h1: dcHhom a b) : D1_cat T.
  eapply (@dcHhom_impl1 T). 
  destruct T; simpl in *.
  exists a.
  exists b.
  exact h1.
Defined.

Definition dc_precat (T: doublecat) : precat.
  set dd := (pbC0 (@C1 cat T) (@C1 cat T)).
  set ee := @iHom_precat cat (D0_cat T).
  econstructor; eauto.
  econstructor.
  exact ee.
Defined.  

Definition dcHcomp'' (T: doublecat) :
    ((@C1 cat T) *_(D0_cat T) (@C1 cat T)) ~> (@C1 cat T).
  destruct T.    
  destruct class as [K1 K2 K3 K4].
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  simpl in *; simpl.
  exact icompI.
Defined.
  
  unfold dc_precat; simpl.
  destruct icompI.
  unfold hom in sort0; simpl in *.
  destruct class as [C]; simpl in *.
  destruct C.
 


Definition dcHcomp'' (T: doublecat) :
  Functor.type (dc_precat T) (@C1 cat T).
  destruct T.    
  destruct class as [K1 K2 K3 K4].
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  simpl in *; simpl.
  unfold dc_precat; simpl.
  destruct icompI.
  unfold hom in sort0; simpl in *.
  destruct class as [C]; simpl in *.
  destruct C.
  
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  simpl.
  destruct sort0.
  simpl in *.
  destruct class as [A B].
  simpl; simpl  in *.
  destruct B.
  eapply F1.
  
  eapply sort0.
  
  instantiate (1:= sort0).
  
  unfold iHom_precat.
  unfold iHom_quiver; simpl.
  exact icompI.
  
  Functor.type (pbC0 (@C1 cat T) (@C1 cat T)) (@C1 cat T).

  (D1_cat T).
  set dd := @icompI cat T.
  simpl in *; simpl.
 Functor.type ((pbC0 (dcInternalHomT T) (dcInternalHomT T)) : precat)
    (D1_cat T). 
  
  Functor.type ((pbC0 (dcInternalHomT T) (dcInternalHomT T)) : precat)
    (D1_cat T). *)

(*
  destruct T.    
  destruct class as [K1 K2 K3 K4].
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  simpl in *; simpl.
  
  assert ( pbC0 C2 C2 ~> C2 ).

 simpl; simpl in *.
 destruct K1; simpl in *; simpl.
 destruct K3.
 simpl in *; simpl.



Definition D1_morph_lift (T: doublecat) (a b: dcHD0Quiver T) 
  (h1: a +> b) : D1_cat T.
  destruct T.
  unfold hhom in h1.
  unfold hom in *; simpl in *.
  eapply D1_morph_liftA; eauto.
Defined.

Definition iHom_morph_liftA  (T: doublecat) (a b: transpose (D0_cat T)) 
  (h1: dcHhom a b) : iHom (D0_cat T) := iHom_lift (D1_morph_liftA h1). 

Definition iHom_morph_lift  (T: doublecat) (a b: dcHD0Quiver T) 
  (h1: a +> b) : iHom (D0_cat T) := iHom_lift (D1_morph_lift h1). 

Definition mk_ptype_auxA (T: doublecat) (a b c: transpose (D0_cat T))
                   (h1: dcHhom a b) (h2: dcHhom b c) :
  commaE.ptype (@tgt cat (D0_cat T) (iHom_morph_liftA h1))
               (@src cat (D0_cat T) (iHom_morph_liftA h2)).
  unfold commaE.ptype.

  have @hh1: D1_cat T := D1_morph_liftA h1.
  have @hh2: D1_cat T := D1_morph_liftA h2.
  
  destruct T; simpl in *.
  destruct class as [K1 K2 K3 K4]; simpl in *; simpl.
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  simpl in *; simpl.

  exists (hh1, hh2).
  subst hh1 hh2.
  simpl; simpl in *.
    
  destruct h1 as [h1 [p1 q1]]; simpl in *; simpl.
  destruct h2 as [h2 [p2 q2]]; simpl in *; simpl.
  rewrite q1.
  rewrite p2.
  auto.
Defined.  

Definition mk_ptype_aux (T: doublecat) (a b c: dcHD0Quiver T)
                   (h1: a +> b) (h2: b +> c) :
  commaE.ptype (@tgt cat (D0_cat T) (iHom_morph_lift h1))
               (@src cat (D0_cat T) (iHom_morph_lift h2)).
  unfold commaE.ptype. 

  have @hh1: D1_cat T := D1_morph_lift h1.
  have @hh2: D1_cat T := D1_morph_lift h2.

  destruct T; simpl in *.
  destruct class as [K1 K2 K3 K4]; simpl in *; simpl.
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  simpl in *; simpl.

  exists (hh1, hh2).
  subst hh1 hh2.
  simpl; simpl in *.
    
  destruct h1 as [h1 [p1 q1]]; simpl in *; simpl.
  destruct h2 as [h2 [p2 q2]]; simpl in *; simpl.
  rewrite q1.
  rewrite p2.
  auto.
Defined.  

Definition mk_prod_auxA (T: doublecat) (a b c: transpose (D0_cat T))
                   (h1: dcHhom a b) (h2: dcHhom b c) :
  (iHom_morph_liftA h1) *_(D0_cat T) (iHom_morph_liftA h2).
  eapply mk_ptype_auxA; eauto.
Defined.  

Definition mk_prod_aux (T: doublecat) (a b c: dcHD0Quiver T)
  (h1: a +> b) (h2: b +> c) :
  (iHom_morph_lift h1) *_(D0_cat T) (iHom_morph_lift h2).
  eapply mk_ptype_aux; eauto.
Defined.  

Definition iHom_prod_liftB (T: doublecat) (x y: iHom (D0_cat T)) :
  iHom (D0_cat T).
  set pp := iprod x y.
  set il := iprodl x y.
  set ir := iprodr x y.
  econstructor.
  instantiate (1 := pp).
  econstructor; eauto.
  econstructor; eauto.
  { destruct x.
    destruct class as [K]; simpl in *; simpl.
    destruct K.
    exact (il \; src).
  }  
  { destruct y.
    destruct class as [K]; simpl in *; simpl.
    destruct K.
    exact (ir \; tgt).
  }  
Defined.  

Definition iHom_prod_liftA (T: doublecat) (a b c: dcHD0Quiver T)
  (h1: a +> b) (h2: b +> c) : iHom (D0_cat T).
  set hh1 := iHom_morph_lift h1. 
  set hh2 := iHom_morph_lift h2.
  eapply (iHom_prod_liftB hh1 hh2).
Defined.  

Definition iHom_prod_liftC (T: doublecat) (x y: iHom (D0_cat T))
  (s: span x y) : iHom (D0_cat T).
  set src1 := @src _ _ x.
  set tgt2 := @tgt _ _ y.
  simpl in *.
  destruct T; simpl in *.
  destruct s; simpl in *.
  destruct bot; simpl in *.
  exists sort0. 
  econstructor; eauto.
  destruct bot2left; simpl in *.
  destruct bot2right; simpl in *.
  econstructor; eauto.
  exact (sort1 \; src1).
  exact (sort2 \; tgt2).
Defined.

(** good *)
Definition iHom_prod_liftE (T: doublecat) (x y: iHom (D0_cat T))
  (s: span (x :> cat) (y :> cat)) : iHom (D0_cat T).
  set src1 := @src _ _ x.
  set tgt2 := @tgt _ _ y.
  simpl in *.
  destruct T; simpl in *.
  destruct s; simpl in *.
  exists bot.
  econstructor; eauto.
  econstructor; eauto.
  exact (bot2left \; src1).
  exact (bot2right \; tgt2).
Defined.

(** good *)
Definition iHom_prod_liftD (T: doublecat) (x y: iHom (D0_cat T)) :
  iHom (D0_cat T).
  set bb := @iprod_pb cat (D0_cat T) x y.
  set ff := @iHom_prod_liftE T x y.
  destruct T; simpl in *.
  specialize (ff bb); eauto.
Defined.

Definition iHom_prod_liftF (T: doublecat) (x y: iHom (D0_cat T)) :
  iHom (D0_cat T).
  set pp := iprod x y.
  set il := iprodl x y.
  set ir := iprodr x y.
  set src1 := @src _ _ x.
  set tgt2 := @tgt _ _ y.
  unfold iprodl, iprodr, iprod in *.
  move: ir il pp.
  set bb := iprod_pb x y.
  simpl in *.
  intros.
  unfold iprod_pb in *.
  unfold pbk in *.
  simpl in *.
  exists (@bot _ _ _ bb).
  econstructor; eauto.
  destruct T; simpl in *.
  econstructor; eauto.
  exact (il \; src1).
  exact (ir \; tgt2).
Defined.  

(* good: based on iHom_prod_liftE or iHom_prod_liftD *)
Definition iHom_prod_liftH (T: doublecat) (a b c: dcHD0Quiver T)
  (h1: a +> b) (h2: b +> c) :
  iHom (D0_cat T).
  set hh1 := D1_morph_lift h1.
  set hhh1 := iHom_lift hh1.
  set hh2 := D1_morph_lift h2.
  set hhh2 := iHom_lift hh2.

  eapply (iHom_prod_liftD hhh1 hhh2).
Defined.
  
Definition iHom_prod_liftG (T: doublecat) (a b c: dcHD0Quiver T)
  (h1: a +> b) (h2: b +> c) :
  iHom (D0_cat T).
  set hh1 := D1_morph_lift h1.
  set hhh1 := iHom_lift hh1.
  set hh2 := D1_morph_lift h2.
  set hhh2 := iHom_lift hh2.
  
  set pp := iprod_pb hhh1 hhh2.
  set il := iprodl hhh1 hhh2.
  set ir := iprodr hhh1 hhh2.
  simpl in *.

  eapply (iHom_prod_liftE pp).
Defined.  

*)




