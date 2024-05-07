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
Fail HB.tag
Definition D0_cat (T: doublecat) : cat := @InternalCat.sort cat T.

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
 
Program Definition ipairCCC (C: cat) {x0 x1 x2 x3 : C}
  (f : x0 ~> x2) (g : x1 ~>_(iHom C0) x3) :
  sigma mr: (x0 *_C0 x1 :> C) ~>_C (x2 *_C0 x3 :> C),
      @iprodl C C0 x0 x1 \; f = mr \; @iprodl C C0 x2 x3 /\
      @iprodr C C0 x0 x1 \; g = mr \; @iprodr C C0 x2 x3. 


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




