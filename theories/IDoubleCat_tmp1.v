Require Import ssreflect ssrfun.
Unset Universe Checking.
From HB Require Import structures cat CatPullbacks InternalCat SADoubleCat.
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
Notation doublecat := (icat cat).

(* Check (doublecat <~> ???) *)
(* HB.structure' Definition DoubleCat := @InternalCat cat.  *)
(*
Print Assumptions doublecat.
About congr1_funext.
*)

(* XXX HB.tag requires 'icat cat' instead of 'doublecat' *)

(* experimented with different definitions of D0_cat (our main
subject). Notice that 'obj cat : U' *)

(* breaks the definition of dcH0Quiver *)
HB.tag Definition D0_catA (T: icat cat) : obj cat :=
  InternalCat.sort T. 
(* behaves as D0_catA *)
HB.tag Definition D0_catB (T: icat cat) : obj cat := T : obj cat. 

(* gives problems further on *)
HB.tag Definition D0_cat (T: icat cat) : U := T : obj cat. 
(* behaves as D0_catC *)
HB.tag Definition D0_catC (T: icat cat) : U :=
  InternalCat.sort T. 


(************************************************************************)

HB.tag Definition D1_cat (T: icat cat) : U := @C1 cat T.

Definition D0_iHom (T: icat cat) : iHom (D0_cat T : cat) := [iHom _].
Definition D1_iHom (T: icat cat) : iHom (D0_cat T : cat) := [iHoms _].

Definition dcHsource (T : doublecat) :
  Functor.type (D1_cat T) (D0_cat T) := [src D1_iHom T].

Definition dcHtarget (T : doublecat) :
  Functor.type (D1_cat T) (D0_cat T) := [tgt D1_iHom T].

Definition dcHunit (T: doublecat) :
  Functor.type (D0_cat T) (D1_cat T) := InternalHomHom.sort (iidI T).

Definition mk_prod_span (T: doublecat) :
  span ((@D1_iHom T) : obj cat) ((@D1_iHom T) : obj cat) :=
  iprod_pb (@D1_iHom T) (@D1_iHom T).

(**********************************************************************)

(*** definition of horizontal homset (corresponds to hhom) *)
(* HB.tag *)
Definition dcHhom (T: icat cat) :
  transpose (D0_cat T) -> transpose (D0_cat T) -> U :=
  fun x y =>
    sigma (h: D1_cat T), dcHsource T h = x /\ dcHtarget T h = y.      

Definition dcHhom_impl1 (T : doublecat) (h : sigma x y, dcHhom x y) :
  D1_cat T := projT1 (projT2 (projT2 h)). 

(*
Definition dcHhom_implF1 (T : doublecat) :
  ((sigma x y, dcHhom x y) : cat) ~> D1_cat T. := projT1 (projT2 (projT2 h)).
*)

Definition dcHhom_impl2 (T : doublecat) (h : D1_cat T) :
  sigma x y, dcHhom x y :=
  existT _ (dcHsource T h) (existT _ (dcHtarget T h)
    (existT _ h (conj erefl erefl))). 
  
Lemma dcHhom_iso1 (T: doublecat) : cancel (@dcHhom_impl2 T) (@dcHhom_impl1 T).
Proof. by []. Qed.
   
Lemma dcHhom_iso2 (T: doublecat) : cancel (@dcHhom_impl1 T) (@dcHhom_impl2 T).
Proof. by move=> [? [? [? []]]]; case: _ /; case: _ /. Qed.

(*
Lemma dcHhom_iso2' (T: doublecat) : cancel (@dcHhom_impl1 T) (@dcHhom_impl2 T).
Proof. unfold cancel.
       move=> [? [? [? []]]]; simpl.
       move=> a b.
       case a; case b; simpl; auto.
Qed.
*)

Definition D1_morph_liftA (T: doublecat) (a b: transpose (D0_cat T)) 
   (h1: dcHhom a b) : D1_cat T := projT1 h1.


Definition mk_prod_auxA (T: doublecat) (a b c: transpose (D0_cat T))
                   (h1: dcHhom a b) (h2: dcHhom b c) :
  (D1_iHom T) *_(D0_cat T : cat) (D1_iHom T) :=
  (existT _ (projT1 h1, projT1 h2) (eq_trans (proj2 (projT2 h1))
                                      (esym (proj1 (projT2 h2))))).


(**********************************************************************)

(** H0 and D0 quivers (HD0Quiver) *)

Definition dcQuiver (T: icat cat) : IsQuiver (D0_cat T) :=
  IsQuiver.Build (D0_cat T) hom.

(* do we really need this instance? 
   the sort of T should coincide with the sort of C0, which should 
   coincide with D0_cat, and this is already a category. *)
HB.instance Definition dcQuiverI (T: icat cat) : IsQuiver (D0_cat T) :=
  dcQuiver T.

(* given D0_cat as base subject and the following def, wrapping should
give us 'IsH0Quiver (D0_cat T)', and thus build an instance of
HD0Quiver for D0_cat *)
Unset Universe Checking.
Definition dcHQuiver (T: icat cat) : IsQuiver (transpose (D0_cat T)) := 
  IsQuiver.Build (transpose (D0_cat T)) (@dcHhom T).
Set Universe Checking.

(* However ... *)
Unset Universe Checking.
(* XXX WRAPPING ERROR: IsH0Quiver.Build is wrong *)
Fail HB.instance Definition dcHQuiverI (T: icat cat) :
   IsQuiver (transpose (D0_cat T)) := dcHQuiver T.

Fail HB.instance Definition dcH0Quiver (T: icat cat) :=
  IsQuiver.Build (transpose (D0_cat T)) (@dcHhom T).

Fail HB.instance Definition dcH0Quiver (T: icat cat) :=
  IsQuiver.Build (transpose (@InternalCat.sort cat T)) (@dcHhom T).
Set Universe Checking.

(* Therefore ... *) 
Unset Universe Checking.
(* as a patch, we manually define the wrapper instance *)
HB.instance Definition dcH0Quiver (T : icat cat) : IsH0Quiver (D0_cat T) :=
  @IsH0Quiver.Axioms_ (D0_cat T) (dcQuiver T) (dcHQuiver T).
Set Universe Checking.

(* just to check *)
Definition dcquiver_d (T: icat cat) : HD0Quiver.type.
  Fail pose xx : Quiver.type := HB.pack T.
  pose xx : IsQuiver (D0_cat T) := dcQuiver T.
  pose yy : IsQuiver (transpose (D0_cat T)) := dcHQuiver T.
  
  econstructor; eauto.
  instantiate (1:= D0_cat T).
  econstructor; eauto.
  instantiate (1:= yy).
  econstructor; eauto.
Defined.

(* just to check *)
Definition dchd0quiver (T : icat cat) : HD0Quiver (D0_cat T).
  econstructor; eauto.
  exact (dcH0Quiver T).
Defined.  

(* HB.about D0_cat. *)

(***********************************************************************)

(** D0 category *)

HB.instance Definition dcD0Precat (T: icat cat) : Quiver_IsPreCat (D0_cat T)
  := Quiver_IsPreCat.Build (D0_cat T) (@idmap (D0_cat T)) (@comp (D0_cat T)).

HB.instance Definition dcD0Cat (T: icat cat) : PreCat_IsCat (D0_cat T)
  := PreCat_IsCat.Build (D0_cat T) (@comp1o (D0_cat T)) (@compo1 (D0_cat T))
      (@compoA (D0_cat T)).


(***********************************************************************)

(** H0 precat *)

(** Horizontal identity *)
Definition H0_cat_idobj (T: icat cat) (a: D0_cat T) : D1_cat T :=
  InternalHomHom.sort (iidI T) a.

Lemma dhSource_iidI (T : icat cat) (a: transpose (D0_cat T)) :
   dcHsource T (H0_cat_idobj a) = a.
Proof.
by have [+ _] := @hom_src _ _ _ _ (iidI T) => /(congr1 (fun f => f a)); apply.
Qed.

Lemma dhTarget_iidI (T : icat cat) (a: transpose (D0_cat T)) :
   dcHtarget T (H0_cat_idobj a) = a.
Proof.
by have [+ _] := @hom_tgt _ _ _ _ (iidI T) => /(congr1 (fun f => f a)); apply.
Qed.

(* H0 identity *)
Definition H0_cat_id (T: icat cat) (a: D0_cat T) : a +> a :=
  existT _ (H0_cat_idobj a) (conj (dhSource_iidI a) (dhTarget_iidI a)).

(** Horizontal composition *)
Definition H0_cat_compobj {T : icat cat} {a b c : transpose (D0_cat T)}
   (h1 : a +> b) (h2 : b +> c) : D1_cat T :=
 InternalHomHom.sort (icompI T) (mk_prod_auxA h1 h2).

Lemma src_hh (T : icat cat) (a b : transpose (D0_cat T)) (h : a +> b) :
  [src D1_iHom T] (projT1 h) = a.
Proof. by case: h => h [/= ->]. Qed.

Lemma tgt_hh (T : icat cat) (a b : transpose (D0_cat T)) (h : a +> b) :
  [tgt D1_iHom T] (projT1 h) = b.
Proof. by case: h => h [/= _ ->]. Qed.
 
Lemma dhSource_icompI (T : icat cat) (a b c : transpose (D0_cat T)) 
   (h1 : a +> b) (h2 : b +> c) :
   dcHsource T (H0_cat_compobj h1 h2) = a.
Proof.
have [+ _] := @hom_src _ _ _ _ (icompI T).
by move => /(congr1 (fun f => f _)) /= -> /=; rewrite src_hh.
Qed.

Lemma dhTarget_icompI (T : icat cat) (a b c : transpose (D0_cat T)) 
   (h1 : a +> b) (h2 : b +> c) :
   dcHtarget T (H0_cat_compobj h1 h2) = c.
Proof.
have [+ _] := @hom_tgt _ _ _ _ (icompI T).
by move => /(congr1 (fun f => f _)) /= -> /=; rewrite tgt_hh.
Qed.

(* H0 composition (this WAS problematic, now it's fine). *)
Definition H0_cat_comp (T : icat cat) (a b c : transpose (D0_cat T)) 
    (h1 : a +> b) (h2 : b +> c) : a +> c :=
  existT _ (H0_cat_compobj h1 h2)
    (conj (dhSource_icompI h1 h2) (dhTarget_icompI h1 h2)).

(* with PreCat: this is right *)
Unset Universe Checking.
Definition dcH0PreCat (T: icat cat) : IsPreCat (transpose (D0_cat T)) :=
  @IsPreCat.Build (transpose (D0_cat T)) (@dcHhom T)
    (@H0_cat_id T) (@H0_cat_comp T).
Set Universe Checking.

(* with quiver_is_precat: this is right *)
Unset Universe Checking.
Definition dcH0QuiverIsPreCat (T: icat cat) :
  Quiver_IsPreCat (transpose (D0_cat T)) :=
  @Quiver_IsPreCat.Build (transpose (D0_cat T)) 
    (@H0_cat_id T) (@H0_cat_comp T).
Set Universe Checking.

(* However... XXX ERROR *)
Unset Universe Checking.
Fail HB.instance Definition dcH0PreCatI (T: icat cat) :=
  dcH0PreCat T.
Fail HB.instance Definition dcH0QuiverIsPreCatI (T: icat cat) :=
  dcH0QuiverIsPreCat T.
Set Universe Checking.

(* H0 precat. manual instantiation of the wrapper works (but it should
have been derived from dcH0QuiverIsPreCatI) *)
Unset Universe Checking.
HB.instance Definition dcIsH0PreCat (T: icat cat) :
  IsH0PreCat (D0_cat T) :=
  @IsH0PreCat.Build (D0_cat T) (dcH0QuiverIsPreCat T).
Set Universe Checking.


(* with PreCat: this is WRONG! why does it typecheck? *)
Unset Universe Checking.
Definition dcH0PreCat' (T: icat cat) : IsPreCat (D0_cat T) :=
  @IsPreCat.Build (D0_cat T) (@dcHhom T)
    (@H0_cat_id T) (@H0_cat_comp T).
Set Universe Checking.

(* with quiver_is_precat: this is WRONG *)
Unset Universe Checking.
Fail Definition dcH0QuiverIsPreCat' (T: icat cat) :
  Quiver_IsPreCat (D0_cat T) :=
  @Quiver_IsPreCat.Build (D0_cat T) 
    (@H0_cat_id T) (@H0_cat_comp T).
Set Universe Checking.


(*******************************************************************)

Definition DH0_comp1o (T: icat cat)
  (a b: transpose (D0_cat T)) (f: a +> b) : idmap \; f = f.
 set hh := @icompo1 cat T.
 simpl in *.
 unfold canonical_iHom in *.
 unfold ipair in hh; simpl in *.
 unfold comp in hh; simpl in *.
 unfold icompI in hh; simpl in *.
 unfold comp; simpl.
 unfold iprodr in *.
 simpl in *. 
 
  (* basically, apply the two sides of hh to (target f, f) and try to
     simplify and invert. on the left handside one should get the
     composition of id and f, on the right handside one should get f
     as second projection.

    PROBLEM: we haven't instantiated icompI and iidI yet *)
Admitted. 

Definition DH0_compo1 (T: icat cat)
  (a b: transpose (D0_cat T)) (f: a +> b) : f \; idmap = f.
 set hh := @icomp1o cat T.
Admitted.

Definition DH0_compoA (T: icat cat)
  (a b c d: transpose (D0_cat T)) (f: a +> b) (g : b +> c) (h : c +> d) :
    f \; (g \; h) = (f \; g) \; h.
  set hh := @icompoA cat T.
Admitted. 

(* HB instance does not work, as above *)
Unset Universe Checking.
Definition dcIsH0Cat (T: icat cat) :
  PreCat_IsCat (transpose (D0_cat T)) :=
  @PreCat_IsCat.Build (transpose (D0_cat T))  
    (@DH0_comp1o T) (@DH0_compo1 T) (@DH0_compoA T).
Set Universe Checking.


(********************************************************************)

(** D1 category *)

(* temporarily reverted to definition to avoid bug-related failure of
dcD1Quiver *)
Definition C1obj (T: icat cat) := D1obj (D0_cat T). 
(* Notation C1obj T := (D1obj (D0_cat T)). *)
(* C1obj (T: icat cat) := Total2 (@dcHhom T). *)

Definition C1obj_impl1 (T : doublecat) (h : C1obj T) :
  D1_cat T := projT1 (this_morph h).

Definition C1obj_impl2 (T : doublecat) (h : D1_cat T) :
  C1obj T := @TT2 _ _ (dcHsource T h) (dcHtarget T h)
                  (existT _ h (conj erefl erefl)). 

Lemma C1obj_iso1 (T: doublecat) : cancel (@C1obj_impl2 T) (@C1obj_impl1 T).
Proof. by []. Qed.

Lemma C1obj_iso2 (T: doublecat) : cancel (@C1obj_impl1 T) (@C1obj_impl2 T).
Proof. unfold cancel.
       move=> x.
       destruct x as [s t m].
       destruct m as [d [l r]].
       case l; case r; simpl; auto.
Qed.       
       
Definition C1hom (T: doublecat) : C1obj T -> C1obj T -> U.
  set h := @hom (D1_cat T).
  intros.
  eapply C1obj_impl1 in X.
  eapply C1obj_impl1 in X0.
  eapply (h X X0).
Defined.

(* this would seem natural *)
HB.instance Definition dcD1QuiverA (T: icat cat) : IsQuiver (D1_cat T) :=
  IsQuiver.Build (D1_cat T) hom.

HB.instance Definition dcD1PrecatA (T: icat cat) : Quiver_IsPreCat (D1_cat T)
  := Quiver_IsPreCat.Build (D1_cat T) (@idmap (D1_cat T)) (@comp (D1_cat T)).

HB.instance Definition dcD1CatA (T: icat cat) : PreCat_IsCat (D1_cat T)
  := PreCat_IsCat.Build (D1_cat T) (@comp1o (D1_cat T)) (@compo1 (D1_cat T))
      (@compoA (D1_cat T)).

(* 
About C1obj.
About D1obj.
HB.about D1obj. *)
(* new command to print out wrappers *)
(* HB.print_wrappers. *)

(* however, if we want to fit in with the definitions in SADoubleCat,
   we need C1obj as subject, not D1_cat.  Indeed, this should give a
   wrapper instance for D1Quiver (does it? it should, anyway) *)
(* PROBLEM: this fails when we switch to C1obj as notation *)
HB.instance Definition dcD1Quiver (T: icat cat) : IsQuiver (C1obj T) :=
  IsQuiver.Build (@C1obj T) (@C1hom T). 

Definition C1_idmap (T: icat cat) : forall a: C1obj T, a ~> a.
  set h := @idmap (D1_cat T).
  intros.
  have @b : D1_cat T.
  { eapply C1obj_impl1; eauto. }
  specialize (h b).
  auto.
Defined.  
   
Definition C1_comp (T: icat cat) :
  forall (a b c: C1obj T), (a ~> b) -> (b ~> c) -> (a ~> c).
  set h := @comp (D1_cat T).
  intros.
  have @a1 : D1_cat T.
  { eapply (C1obj_impl1 a). }
  have @b1 : D1_cat T.
  { eapply (C1obj_impl1 b). }
  have @c1 : D1_cat T.
  { eapply (C1obj_impl1 c). }
  specialize (h a1 b1 c1).
  auto.
Defined.  

HB.instance Definition dcD1Precat (T: icat cat) : Quiver_IsPreCat (C1obj T)
  := Quiver_IsPreCat.Build (C1obj T) (@C1_idmap T) (@C1_comp T).

Definition C1_comp1o (T: icat cat) :
  forall (a b : C1obj T) (f : a ~> b), idmap \; f = f.
  set h := @comp1o (D1_cat T).
  intros.
  have @a1 : D1_cat T.
  { eapply (C1obj_impl1 a). }
  have @b1 : D1_cat T.
  { eapply (C1obj_impl1 b). }
  have @f1 : a1 ~> b1.
  { auto. }
  specialize (h a1 b1 f1).
  auto.
Defined.  

Definition C1_compo1 (T: icat cat) :
  forall (a b : C1obj T) (f : a ~> b), f \; idmap = f.
  set h := @compo1 (D1_cat T).
  intros.
  have @a1 : D1_cat T.
  { eapply (C1obj_impl1 a). }
  have @b1 : D1_cat T.
  { eapply (C1obj_impl1 b). }
  have @f1 : a1 ~> b1.
  { auto. }
  specialize (h a1 b1 f1).
  auto.
Defined.  

Definition C1_compoA (T: icat cat) :
  forall (a b c d : C1obj T) (f : a ~> b) (g : b ~> c) (h : c ~> d),
    f \; (g \; h) = (f \; g) \; h.
  set h := @compoA (D1_cat T).
  intros.
  have @a1 : D1_cat T.
  { eapply (C1obj_impl1 a). }
  have @b1 : D1_cat T.
  { eapply (C1obj_impl1 b). }
  have @c1 : D1_cat T.
  { eapply (C1obj_impl1 c). }
  have @d1 : D1_cat T.
  { eapply (C1obj_impl1 d). }
  have @f1 : a1 ~> b1.
  { auto. }
  have @g1 : b1 ~> c1.
  { auto. }
  have @h1 : c1 ~> d1.
  { auto. }
  specialize (h a1 b1 c1 d1 f1 g1 h1).
  auto.
Defined.  

HB.instance Definition dcD1Cat (T: icat cat) : PreCat_IsCat (C1obj T)
  := PreCat_IsCat.Build (C1obj T) (@C1_comp1o T) (@C1_compo1 T)
      (@C1_compoA T).


(*
Definition 

Definition C1obj_impl1F (T : doublecat) : (C1obj T : cat) ~> D1_cat T.
  econstructor; eauto.
  instantiate (1:= @C1obj_impl1 T).
  econstructor; eauto.
*)  





(* it should now be possible to derive automatically a DDCat (which
includes D0 cat, D1 cat and H0 quiver) *)
(* HB.about D0_cat. 

HB: D0_cat is canonically equipped with structures:
    - Cat
      (from "(stdin)", line 673)
    - PreCat
      (from "(stdin)", line 672)
    - Quiver
      (from "(stdin)", line 44)
    - HD0Quiver
      (from "(stdin)", line 54)
    - H0PreCat
      (from "(stdin)", line 721)
*)
(* However, D1quiver, D1PreCat and D1Cat are missing *)

(*
Definition HC1obj_impl1 (T : doublecat) : (C1obj T : cat) ~> (D1_iHom T : cat).
*)

(*********************************************************************)

(** Functors *)

(* this works, and is the same as dcHsource, but the type is unclear *)
Definition dcHS_exp1 (T: icat cat) : @C1 cat T ~>_cat _   :=
  @src cat _ (D1_iHom T).
(* Check dcHS_exp1. *)
Lemma xxx (T: icat cat) : dcHS_exp1 T = dcHsource T.
  auto.
Qed.  
Fail Definition dcHS_exp2 (T: icat cat) : @C1 cat T ~>_cat D0_cat T :=
  (* dcHsource T. *)
  @src cat _ (D1_iHom T).

Definition dcHSourceA (T: icat cat) :
  @C1 _ T ~>_cat D0_cat T.
  set h := @src cat _ (D1_iHom T). 
  unfold D0_cat in *.
  unfold D1_iHom in h; simpl in *. 
  destruct h as [hh class0].
  destruct T as [TT class].
  destruct TT as [sortT classT]; simpl in *.
  destruct classT as [TT1 TT2 TT3]; simpl in *.
  destruct TT1.
  destruct TT2.
  destruct TT3.
  simpl in *.
  econstructor.
  instantiate (1:= hh); auto.
Defined.  

Definition dcHTargetA (T: icat cat) :
  @C1 _ T ~>_cat D0_cat T.
  set h := @tgt cat _ (D1_iHom T). 
  unfold D0_cat in *.
  unfold D1_iHom in h; simpl in *. 
  destruct h as [hh class0].
  destruct T as [TT class].
  destruct TT as [sortT classT]; simpl in *.
  destruct classT as [TT1 TT2 TT3]; simpl in *.
  destruct TT1.
  destruct TT2.
  destruct TT3.
  simpl in *.
  econstructor.
  instantiate (1:= hh); auto.
Defined.  

Definition dcHUnitA (T: icat cat) :
 D0_cat T ~>_cat @C1 _ T. 
  set h := @iidI cat T. 
  unfold D0_cat in *.
  unfold canonical_iHom in *.
  simpl in *.
  unfold trivial_iHom in *.
  destruct h as [hh class0].
  destruct T as [TT class].
  destruct TT as [sortT classT]; simpl in *.
  destruct classT as [TT1 TT2 TT3]; simpl in *.
  destruct TT1.
  destruct TT2.
  destruct TT3.
  simpl in *.

  destruct class as [K1 K2 K3 K4].
  destruct K1 as [C2]; simpl in *; simpl.   
  destruct K2 as [[[ src0 tgt0 ]]].
  destruct K3.
  destruct K4.
  simpl in *; simpl.   
   
  destruct class0 as [[E1 E2]]; simpl in *.
  econstructor.
  instantiate (1:= hh); auto.
  destruct hh.
  simpl in *.
  eapply class.
Defined.  

Definition dcHCompA (T: icat cat) :
 (@C1 _ T) *_(D0_catC T : cat) (@C1 _ T) ~>_cat @C1 _ T. 
  unfold D0_catC.
  eapply (@icompI cat T). 
Defined.
  
Fail Definition dcHCompA (T: icat cat) :
 (@C1 _ T) *_(D0_cat T : cat) (@C1 _ T) ~>_cat @C1 _ T. 

Definition dcHSourceB (T: icat cat) : D1_iHom T ~>_(obj cat) (D0_cat T : cat).
  eapply (dcHSourceA T).
Defined.  

(* what we actually need *)

Definition dcHSourceC (T: icat cat) :
  Functor.type (C1obj T) (D0_cat T).
Proof.
have @ff := (@dcHsource T : Functor.type _ _).
set qq :=  fun x => @C1obj_impl1 T x.
set hh := fun x => ff (qq x).
econstructor.
instantiate (1:= hh).
destruct ff.
destruct class.
econstructor; eauto.
(*
Definition dcHSourceC (T: icat cat) :
  Functor.type (C1obj T) (D0_cat T).
Proof.
have := (@dcHsource T : Functor.type _ _).
case: T => [? [? ? ? ?]] /=.
rewrite /D1_cat/= /C1obj /D0_cat/= /D1obj/=.
*)
Admitted.
Fail HB.instance Definition _ (T : icat cat) :=
  Functor.copy (@HSource (D0_cat T)) (@dcHSourceC T).

(* exact. *)
(*   unfold C1obj. *)
(*   unfold D1obj. *)

(*   (* PROBLEM: HSource should be recognized as a functor,  *)
(*      given D0_cat is an HD0quiver *) *)
(*   Fail set h := (@HSource (D0_cat T) : (C1obj T : cat) ~>_cat D0_cat T). *)
(*   set h1 := (@HSource (D0_cat T)). *)

(*   (* alternative course *) *)
(*   set h2 := @src cat _ (D1_iHom T).  *)
(*   unfold D0_cat in *. *)
(*   unfold D1_iHom in h2; simpl in *.  *)

(*   unfold D0_cat in *; simpl. *)
(*   unfold D1obj in *; simpl. *)
(*   unfold hhom in *; simpl in *. *)
(*   (* PROBLEM: Total2 hom and C1 should be equated *) *)
(* Admitted. *)

Definition dcHTargetC (T: icat cat) : (C1obj T : cat) ~> D0_cat T.
Admitted.

Definition dcHUnitC (T: icat cat) : D0_cat T ~>_cat C1obj T. 
Admitted. 

(* if wrapping is automatic, in order to get SFuncton and TFunctor we
just need to give the lifted instances of Functor. HB knows which one
to wrap as SFunctor and TFunctor because the subject is different for
the two mixins. But both depend on the Total2 structure. *)

(* one possibility is to prove C1obj to be an InternalHom. It seems
rather problematic thought, as T already contains C1 as internal hom.
*)
(*
Definition dcInternalHom (T: icat cat) :
  isInternalHom cat (D0_cat T: cat) (C1obj T : cat).
*)

Fail Definition dcHCompC (T: icat cat) :
 (D1_iHom T) *_(D0_cat T: cat) (D1_iHom T) ~>_cat C1obj T. 

(* alternatively, we can define the product on C1obj. However, this is
too restrictive *)
Definition dcProd (T: icat cat) :
  span (C1obj T: cat) (C1obj T) :=
  pbk (Cospan (dcHTargetC T) (dcHSourceC T)). 
  

(*********************************************************************)
(*
Lemma hsource_eq (T: icat cat) : @HSource (D0_cat T) = dcHSourceC T.
  unfold HSource. dcHSourceC.
*)
(** deriving a STUFunctor *)
Definition dc2stuf (T: icat cat) : STUFunctor (D0_cat T).
  have @D0 : cat := D0_cat T.

  have @D1 : cat := C1obj T. 

  econstructor.
  econstructor; eauto.
Admitted.

Fail HB.instance Definition dc2stuf' (T: icat cat) :
  STUFunctor (D0_cat T) := dc2stuf T.


(********************************************************************)

Require Import SADCat_xeqH1.

HB.tag Definition dcH1obj (T: icat cat) : U := Total2 (@hom (D0_cat T)).
(* := H1obj (D0_cat T) *)

(* the typing needs to be fixed, but first of all we need the STUFunctor instance *)
Fail Definition dcH1hom (T: icat cat) (a b: dcH1obj T) := @H1hom (D0_cat T) a b.

Program Definition dcH1hom (T: icat cat) (a b: dcH1obj T) : U :=
  sigma (h1: dcHhom (source a) (source b)) (h2: dcHhom (target a) (target b)) 
    (hh: C1hom (TT2 h1) (TT2 h2)), 
    (@dcHSourceC T) <$> hh = this_morph a /\
    (@dcHTargetC T) <$> hh = this_morph b. 
Obligation 1.
intros.
(* PROBLEM: we haven't properly defined dcHSourceC and dcHTargetC yet *)
Fail unfold dcHSourceC.
Admitted. 
Obligation 2.
intros.
Admitted.
Obligation 3.
intros.
Admitted.
Obligation 4.
Admitted.

(* Lemma Unit_source (T: icat cat) : *)

(********************************************************************)

(** USELESS *)
(*
Lemma ext_functor (A B: cat) (f: A ~> B) : @Functor A B (Functor.sort f).
  destruct f; simpl.
  auto.
Defined.  
  
Lemma ext_prefunctor (A B: cat) (f: A ~> B) :
  @PreFunctor A B (Functor.sort f).
  destruct f; simpl.
  destruct class.
  econstructor; eauto.
Defined.  

Lemma ext_prefunctor_isfunctor (A B: cat) (f: A ~> B) :
  @PreFunctor_IsFunctor A B (Functor.sort f).
  destruct f; simpl.
  destruct class.
  eauto.  
Defined.  

Definition dcSPreFunctor (T: icat cat) :
  IsPreFunctor (C1obj T : cat) (D0_cat T) (dcHSourceC T).
  eapply ext_prefunctor.
Defined.

HB.instance Definition dcSPreFunctor' (T: icat cat) :
  IsPreFunctor (C1obj T : cat) (D0_cat T) (dcHSourceC T) :=
  dcSPreFunctor T.
*)

(*  
  { 
    set HH := (ext_prefunctor_isfunctor (dcHTargetC T)).
    econstructor; eauto.
    destruct HH.
    econstructor; eauto.
    unfold C1obj in *.
    exact F1.
    auto.
  }
    
  Set Printing All.
  exact HH.
  
  
  have @SR : Functor.type (D0_cat T) (C1obj T).
  { exact (ext_functor (dcHSourceC T)).
  
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
  { eapply (H0PreCatD T). }

  have DD : DDCat (D0_cat T).
  econstructor; eauto.
  econstructor; eauto.
  admit.    
  admit.
 
  unfold D0_cat in *.
  simpl in *.
  unfold D1_cat in *.
  subst D0 D1.
  simpl in *.

  set C := @InternalCat.sort cat T.
  econstructor; eauto.
  instantiate (1:= C).
*)

(*********************************************************************)

(*
Definition dcHSourceA (T: icat cat) : (D1_cat T: cat) ~>_cat (D0_cat T: cat).  
  set h := @src cat _ (D1_iHom T).
  simpl in h.
  unfold D1_cat.
  unfold D0_cat in *.

  
  unfold src in *.
  simpl in *.
  
(*  destruct h as [ff class].
  econstructor.
  instantiate (1:=ff).
  destruct class as [K1 K2].
  econstructor; eauto.
  destruct K1 as [Fhom0].
  destruct K2.
  econstructor; eauto.
  intros.
  specialize (F1 a).
*)

  destruct T.
  destruct class as [K1 K2 K3 K4].
  destruct K1 as [C2]; simpl in *; simpl.   
  destruct K2 as [[[ src0 tgt0 ]]].
  destruct K3.
  destruct K4.
  simpl in *; simpl.   

  unfold D0_cat in *.
  simpl in *.

  unfold C1.
  simpl.
  unfold C1 in *.
  simpl in *.
  
  exact h.
  
  unfold Fhom in *.
  simpl in *.
  simpl.

  assert (@C1 cat _ _ = C2).
  exact F1.
  
  instantiate (1:=K1).
  exact h.
  
  Check (D1_iHom T: obj cat).
Admitted.   
*)

(********************************************************************)
(*
Definition dcHSource (T: icat cat) : (C1obj T : cat) ~> D0_cat T.
  set h := @src cat (D0_cat T : cat) (D1_iHom T).
  { destruct T.    
    destruct class as [K1 K2 K3 K4].
    subst D0 D1.
    simpl; simpl in *.
    
    destruct K1; simpl in *; simpl.
   
    destruct K2 as [[[src0 tgt0]]];
      simpl in *; simpl.
    
    eapply src0.
  }
*)
(*
  destruct T.
  econstructor.
  instantiate (1:=h).
  destruct class as [K1 K2 K3 K4].
  simpl; simpl in *.
  destruct K1 as [C2]; simpl in *; simpl.   
  destruct K2 as [[[ src0 tgt0 ]]].
  destruct K3.
  destruct K4.
  simpl in *; simpl.   
    
  destruct h.
  simpl; simpl in *.
  
  destruct class as [K1 K2]; simpl in *.
  econstructor.
  unfold D1_cat.
  simpl.
  destruct K1.
  destruct K2.
  econstructor.
  exact F1.
*)

(********************************************************************)
(********************************************************************)

(* we can derive HD0Quiver (part of the STUFunctor def) *)
Definition dcHD0QuiverD (T: doublecat) : HD0Quiver (D0_cat T).
  set X := dcH0QuiverD T.
  destruct T.
  econstructor; eauto.
  instantiate (1:=X).   (* wrapped instance *)
  econstructor; eauto.
Defined.

(* sanity check.
   XXX non-forgetful inheritance warning, expected as this should be
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

(* XXX there should be no need for dcHD0Quiver *)
Definition H0_cat_Id (T: doublecat) (a: dcHD0Quiver T) : a +> a.
  destruct T; simpl in *.
  unfold hhom.
  unfold hom; simpl.
  eapply H0_cat_id.
Defined.  

Definition H0_cat_Comp (T: doublecat) (a b c: dcHD0Quiver T)
  (h1: a +> b) (h2: b +> c) : a +> c.
  destruct T.
  unfold hhom in *.
  unfold hom in *; simpl in *.
  eapply H0_cat_comp; eauto.
Defined.  


(********************************************************************)

(** deriving a STUFunctor *)
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
  { eapply (H0PreCatD T). }

  have DD : DDCat (D0_cat T).
  econstructor; eauto.
  econstructor; eauto.
  admit.    
  admit.
 
  unfold D0_cat in *.
  simpl in *.
  unfold D1_cat in *.
  subst D0 D1.
  simpl in *.

  set C := @InternalCat.sort cat T.
  econstructor; eauto.
  instantiate (1:= C).

(*  pose XT : STUFunctor.type := HB.pack C DD SR TG UN H0PC. *)
Admitted.

(*  
  destruct T.
  destruct class as [K1 K2 K3 K4].
  simpl in *.
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  simpl in *.

  destruct TG as [tt [p1 p2]]; simpl in *.
  destruct p1.
  destruct p2.
  
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  unfold HTarget; simpl.
  intro; simpl.
  pose XT : STUFunctor.type := HB.pack T SR TG UN H0PC. 
*)
  
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

(*
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
*)
(*
Fail Definition dcH0PreCatD' (T: icat cat) :
  IsH0PreCat (dcHD0Quiver T).

Fail Definition dcH0PreCatD' (T: icat cat) :
  IsH0PreCat (D0_cat T).

(* non-forgetful inheritance warning *)
HB.instance Definition dcH0PreCat (T: doublecat) :
  IsPreCat (transpose_D0 T) := dcH0PreCatD T.  
*)

(***********************************************************************)
(***********************************************************************)
(*** NOT NEEDED ********************************************************)


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

(**********************************************************************)

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

(*
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
*)

(***********************************************************************)

(*
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
*)

(**********************************************************************)

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




