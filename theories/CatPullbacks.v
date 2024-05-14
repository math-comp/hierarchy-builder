Require Import ssreflect ssrfun.
Unset Universe Checking.
From HB Require Import structures cat.
Set Universe Checking.
Require Import Coq.Program.Equality.
Require Import FunctionalExtensionality.

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

(* Require Import FunctionalExtensionality. *)
(* local version of equal_f *)
Lemma funext_equal_f A B (f g: A -> B) :
  f = g -> forall x : A, f x = g x.
  intros. rewrite H; auto.
Qed.  


(**************************************************************************)

(** The projections of a binary product of categoris are functors *)

Definition fst0 {A B: U} : (A * B)%type -> A := fst.
Definition snd0 {A B: U} : (A * B)%type -> B := snd.

HB.instance Definition fst0_IsPreFunctor (C D : quiver) :=
  IsPreFunctor.Build (C * D)%type C fst0
     (fun (a b : C * D) (f : a ~> b) => f.1).
HB.instance Definition snd0_IsPreFunctor (C D : quiver) :=
  IsPreFunctor.Build (C * D)%type D snd0
    (fun (a b : C * D) (f : a ~> b) => f.2).
Lemma fst0_IsFunctor_lemma (C D: precat) :
  PreFunctor_IsFunctor ((C * D)%type: precat) C fst0.
  econstructor; eauto.
Defined.  
Lemma snd0_IsFunctor_lemma (C D: precat) :
  PreFunctor_IsFunctor ((C * D)%type: precat) D snd0.
  econstructor; eauto.
Defined.  
HB.instance Definition fst0_IsFunctor (C D : precat) :=
  fst0_IsFunctor_lemma C D.
HB.instance Definition snd0_IsFunctor (C D : precat) :=
  snd0_IsFunctor_lemma C D.

Program Definition fstF {A B: precat} : ((A * B)%type : precat) ~> A.
econstructor; eauto.
econstructor; eauto.
eapply (fst0_IsFunctor A B).
Defined.

Program Definition sndF {A B: precat} : ((A * B)%type : precat) ~> B.
econstructor; eauto.
econstructor; eauto.
eapply (snd0_IsFunctor A B).
Defined.

(***************************************************************************)

Module commaE. 

Section homcommaE.
Context {C D E : precat} (F : C ~> E) (G : D ~> E).

(** the type of pullback objects in Cat *)
Definition ptype := { x : C * D & F x.1 = G x.2 }.

Definition hom_psubdef (a b : ptype) := {
    f : tag a ~> tag b &
     ecast2 x y (x ~> y) (tagged a) (tagged b) (F <$> f.1) = (G <$> f.2) }.
#[export]
HB.instance Definition _ := IsQuiver.Build ptype hom_psubdef.

(**********************************************************************)

Definition hom_psubdef' (a b : ptype) := {
    f : tag a ~> tag b &
          ecast2 x y (x ~> y) (tagged a) (tagged b) ((fstF \; F) <$> f) =
            (sndF \; G) <$> f }.

Program Definition functor_ptype_eq 
  (x y: ptype) :=
    (forall (m: hom x y),
        @Fhom C E F (tag x).1 (tag y).1 (tag m).1 =
          @Fhom D E G (tag x).2 (tag y).2 (tag m).2).
Obligation 1.
destruct x as [[x1 x2] ex].
destruct y as [[y1 y2] ey].
auto.
Defined.
Obligation 2.
destruct x as [[x1 x2] ex].
destruct y as [[y1 y2] ey].
auto.
Defined.

Definition p2type := sigma (p: ptype * ptype),
                      functor_ptype_eq (fst p) (snd p).

End homcommaE.

Arguments hom_psubdef /.

Section commaS.
Context {C D E : cat} (F : C ~> E) (G : D ~> E).
Notation ptype := (ptype F G).

Program Definition idmap_psubdef (a : ptype) : a ~> a := @Tagged _ idmap _ _.
Next Obligation.
  destruct a.
  destruct x.
  simpl in *; simpl.  
  rewrite F1.
  rewrite F1.
  simpl.
  destruct e; auto.
Defined.

Program Definition comp_psubdef (a b c : ptype)
  (f : a ~> b) (g : b ~> c) : a ~> c :=
  @Tagged _ (tag f \; tag g) _ _.
Next Obligation.
  intros; simpl.  
  rewrite Fcomp.
  rewrite Fcomp.

  destruct f as [ff ef].
  destruct g as [gg eg].
  destruct ff as [f1 f2].
  destruct gg as [g1 g2].
  simpl; simpl in *.
  destruct a as [aa ea].
  destruct aa as [a1 a2].
  destruct b as [bb eb].
  destruct bb as [b1 b2].
  destruct c as [cc ec].
  destruct cc as [c1 c2].
  simpl; simpl in *.

  rewrite -eg.
  rewrite -ef.
  clear ef eg.
  
  dependent destruction ea.
  dependent destruction eb.
  dependent destruction ec.
  auto.  
Defined.  

#[export]
HB.instance Definition _ := IsPreCat.Build ptype idmap_psubdef comp_psubdef.
Arguments idmap_psubdef /.
Arguments comp_psubdef /.

Lemma pcomma_homeqP (a b : ptype) (f g : a ~> b) :
  projT1 f = projT1 g -> f = g.
Proof.
case: f g => [f fP] [g +]/= eqfg; case: _ / eqfg => gP.
by congr existT; apply: Prop_irrelevance.
Qed.

Lemma pcomma_is_cat : PreCat_IsCat ptype.
Proof.
by split=> [[a fa] [b fb] [*]|[a fa] [b fb] [*]|*];
   apply/pcomma_homeqP; rewrite /= ?(comp1o, compo1, compoA).
Qed.

(** ptypes form a category *)
#[export]
HB.instance Definition pcomma_cat := pcomma_is_cat.

End commaS.

Module Exports.
 HB.reexport.
End Exports.
  
End commaE.

Import commaE.
Import commaE.Exports.

(** the projections pcat_prj1, pcat_prj2 of a ptype are functors *)

Definition pcat_prj1 {C D E F G} (P: @commaE.ptype C D E F G) : C :=
  fst (tag P).

Definition pcat_prj2 {C D E F G} (P: @commaE.ptype C D E F G) : D :=
  snd (tag P).

Program Definition pcat_prj1_isPreFunctor {C D E F G} :=
  IsPreFunctor.Build _ _ (@pcat_prj1 C D E F G) _.
Obligation 1. by move=> C D E F G a b [f Y]; exact f.1. Defined.

Program Definition pcat_prj2_isPreFunctor {C D E F G} :=
  IsPreFunctor.Build _ _ (@pcat_prj2 C D E F G) _.
Obligation 1. by move=> C D E F G a b [f Y]; exact f.2. Defined.

HB.instance Definition _ {C D E F G} : IsPreFunctor _ _ pcat_prj1 :=
  @pcat_prj1_isPreFunctor C D E F G.

HB.instance Definition _ {C D E F G} : IsPreFunctor _ _ pcat_prj2 :=
  @pcat_prj2_isPreFunctor C D E F G.

Program Definition pcat_prj1_isFunctor {C D E: cat} {F G} :=
  PreFunctor_IsFunctor.Build _ _ (@pcat_prj1 C D E F G) _ _.
Obligation 2.
move=> C D E F G a b c0 f g.
destruct a.
destruct b.
destruct c0.
destruct f.
destruct g.
simpl; simpl in *.
unfold Fhom.
simpl. auto.
Defined.

Program Definition pcat_prj2_isFunctor {C D E: cat} {F G} :=
  PreFunctor_IsFunctor.Build _ _ (@pcat_prj2 C D E F G) _ _. 
Obligation 2.
move=> C D E  F G a b c0 f g.
destruct a.
destruct b.
destruct c0.
destruct f.
destruct g.
simpl; simpl in *.
unfold Fhom.
simpl. auto.
Defined.

HB.instance Definition _ {C D E F G} : PreFunctor_IsFunctor _ _ pcat_prj1 :=
  @pcat_prj1_isFunctor C D E F G.

HB.instance Definition _ {C D E F G} : PreFunctor_IsFunctor _ _ pcat_prj2 :=
  @pcat_prj2_isFunctor C D E F G.


(** the projection pcat_tag of a ptype is a functor *)

Definition pcat_tag {C D E F G} (P: @commaE.ptype C D E F G) : (C * D) :=
  (pcat_prj1 P, pcat_prj2 P).

Program Definition pcat_tag_isPreFunctor {C D E F G} :=
  IsPreFunctor.Build _ _ (@pcat_tag C D E F G) _.
Obligation 1. by move=> C D E F G a b [f Y]. Defined.

HB.instance Definition _ {C D E F G} : IsPreFunctor _ _ pcat_tag :=
  @pcat_tag_isPreFunctor C D E F G.

Program Definition pcat_tag_isFunctor {C D E: cat} {F G} :=
  PreFunctor_IsFunctor.Build _ _ (@pcat_tag C D E F G) _ _.

HB.instance Definition _ {C D E F G} : PreFunctor_IsFunctor _ _ pcat_tag :=
  @pcat_tag_isFunctor C D E F G.

Lemma pcat_tag_simpl {C D E F G} : @pcat_tag C D E F G = tag. 
  eapply funext; intros.
  destruct t as [[a b] e]; auto.
Qed.  


(************************************************************************)

(*** CATEGORIES WITH PULLBACKS *)

(* Ideally span is in fact expanded and the final mixin has
a pb : forall A B, cospan A B -> C
but it is not clear how to do that yet
*)
(* pullback operator *)
HB.mixin Record HasPBop C of Cat C := {
  pbk : forall (A B: C), cospan A B -> span A B
  }.
#[short(type="pbop")]
HB.structure Definition PBop :=
  {C of HasPBop C }. 
Arguments pbk {_ _ _}.

(* category with all prepullbacks *)
(* Problematic: wrapping a class (PBop) instead of a mixin *)
#[wrapper]
HB.mixin Record HasPreBCat C of PBop C : Type := {
  is_ppbk : forall (a b : C) (c : cospan a b),
      isPrePullback C a b c (pbk c)
  }.
#[short(type="prepbcat")]
HB.structure Definition PreBCat :=
  {C of HasPreBCat C}.

(* category with all pullbacks *)
#[wrapper]
HB.mixin Record HasPBCat C of PBop C & HasPreBCat C : Type := {
  is_tpbk : forall (a b : C) (c : cospan a b),
     prepullback_isTerminal C a b c (pbk c)
  }.
#[short(type="pbcat")]
HB.structure Definition PBCat :=
  {C of HasPBCat C}.


(*******************************************************************)

(**** Cat has all pullbacks *)

(** pullback operator in Cat *)
Lemma cat_pbop : HasPBop cat.
  econstructor; intros.
  destruct H; simpl in *.

(*  set (PB := catprod left2top right2top). *)
  set (PB := (@commaE.ptype A B top left2top right2top : cat)). 

  assert (PB ~> A) as L1.
  { econstructor.
    econstructor.
    eapply pcat_prj1_isFunctor.
  }

  assert (PB ~> B) as R1.
  { econstructor.
    econstructor.
    eapply pcat_prj2_isFunctor.
  }

  exact (@Span cat A B PB L1 R1).
Defined.
HB.instance Definition cat_HasPBop := cat_pbop.

(** Cat has all prepullbacks *)
Lemma cat_preb (a b: cat) (c: cospan a b) :
   isPrePullback cat a b c (pbk c).
Proof.
constructor; case: c => /= c l r.
pose p1 := @pcat_prj1 _ _ _ l r.
pose p2 := @pcat_prj2 _ _ _ l r.
have @l1r2 : (l \o p1)%FUN =1 (r \o p2)%FUN by exact: tagged.
apply/functorPcast => /= -[[/= a0 b0] ab0] [[/= a1 b1] ab1].
by case=> -[/= a01 b01 larb] /=; rewrite /Fhom/= -larb.
Qed.
HB.instance Definition _ (a b: cat) (c: cospan a b) := @cat_preb a b c.


(* alternate proof of cat_preb - for comparison *)
Lemma cat_preb' :
  forall (a b: cat) (c: cospan a b),
    isPrePullback cat a b c (pbk c).
  intros.

  remember (pbk c) as K.

  destruct c; simpl in *; simpl.  
  econstructor; simpl.
  unfold comp; simpl.

  destruct K.
  have C1 : (bot2left \; left2top =1 bot2right \; right2top).
  { simpl.
    unfold eqfun; simpl.
    intros.
    inversion HeqK; subst.
    clear HeqK.

    dependent destruction H2.
    dependent destruction H1.
    simpl.
    destruct x as [[x1 x2] e].
    simpl; simpl in *.
    unfold pcat_prj1.
    unfold pcat_prj2.
    simpl; auto.
  }

  simpl; simpl in *. 
  
  unfold pbk in HeqK.
  simpl in HeqK.
  inversion HeqK; subst.
  clear HeqK.
  dependent destruction H2.
  dependent destruction H1.
  simpl; simpl in *.

  unfold pcat_prj1.
  unfold pcat_prj2. 
  unfold ssrfun.comp.
  unfold eqfun in C1.

  cut (forall x : ptype left2top right2top, 
          left2top (tag x).1 = right2top (tag x).2).

  2: { intros.
       specialize (C1 x).
       simpl in *; simpl.
       rewrite C1.
       auto.
     }
  
  intros.
  eapply funext in H.
  eauto.

  rewrite H.
  auto.
  clear H.
  
  eapply functorPcast.
  instantiate (1:=C1).
  intros.
  destruct f.
  destruct x.
  simpl in *; simpl.
  destruct a0.
  destruct b0.
  simpl in *; simpl.
  destruct x.
  destruct x0.
  simpl in *; simpl.
  
  assert ((C1 (existT (fun x : a * b => left2top x.1 = right2top x.2)
                 (s, s0) e0)) =  e0) as H.
  eapply Prop_irrelevance.
  rewrite H.
  
  assert ((C1
             (existT (fun x : a * b => left2top x.1 = right2top x.2)
                (s1, s2) e1)) = e1) as H1.
  eapply Prop_irrelevance.
  rewrite H1.
  rewrite e.
  simpl.
  reflexivity.
Defined.  


(*************************************************************************)

(** joins together two functors; some analogy with pushouts *)
Definition fsplitter (A B C: cat) (F: A ~> B) (G: A ~> C) :
  A -> ((B * C)%type : cat) := fun x: A => (F x, G x).

Program Definition fsplitter_Fhom (A B C: cat)
  (F: A ~> B) (G: A ~> C) :
  forall (a b : A), (a ~> b) -> (fsplitter F G a ~> fsplitter F G b).
intros.
unfold fsplitter.
unfold hom; simpl.
unfold prod_hom_subdef; simpl.
split.
unfold hom in F, G; simpl in *.
eapply Fhom; auto.
eapply Fhom; auto.
Defined.

Lemma fsplitter_IsPreFunctor_lemma (A B C: cat)
  (F: A ~> B) (G: A ~> C) :
  IsPreFunctor A ((B * C)%type : cat) (@fsplitter _ _ _ F G).
  econstructor; eauto.
  intros.
  unfold fsplitter, hom; simpl.
  unfold prod_hom_subdef; simpl.
  split.
  unfold hom in F, G; simpl in *.
  eapply Fhom; auto.
  eapply Fhom; auto.
Defined.  
(** fsplitter is a prefunctor *)  
HB.instance Definition fsplitter_IsPreFunctor
  (A B C: cat) (F: A ~> B) (G: A ~> C) :=
  fsplitter_IsPreFunctor_lemma F G.

Lemma fsplitter_IsFunctor_lemma (A B C: cat) (F: A ~> B) (G: A ~> C) :
  PreFunctor_IsFunctor A ((B * C)%type : cat) (fsplitter F G).
  econstructor; eauto.
  intros; unfold fsplitter; simpl.
  unfold hom in F, G; simpl in *.
  unfold Fhom; simpl.
  rewrite F1.
  rewrite F1.
  unfold idmap; simpl.
  auto.
  intros; unfold fsplitter; simpl.
  unfold hom in F, G; simpl in *.
  unfold Fhom; simpl.
  rewrite Fcomp.
  rewrite Fcomp.
  auto.
Defined.
(** fsplitter is a functor *)  
HB.instance Definition fsplitter_IsFunctor
  (A B C: cat) (F: A ~> B) (G: A ~> C) :=
  fsplitter_IsFunctor_lemma F G.

Program Definition fsplitter_morph (A B C: cat)
  (F: A ~> B) (G: A ~> C) : A ~> ((B * C)%type : cat).
unfold hom; simpl.
exact (fsplitter F G). 
Defined.


(* Require Import FunctionalExtensionality. *)
Lemma mediating_fun_ext_proj1 (A B C: cat)
  (F1: A ~> B) (G1: A ~> C) :
  forall (a1 a2 : A) (hh: a1 ~> a2),
     ((fsplitter F1 G1: Functor.type _ _) \; fstF) <$> hh = (F1 <$> hh).
  intros.
  unfold fsplitter.
  simpl; auto.
Defined. 

Lemma mediating_fun_ext_proj2 (A B C: cat)
  (F1: A ~> B) (G1: A ~> C) :
  forall (a1 a2 : A) (hh: a1 ~> a2),
     ((fsplitter F1 G1: Functor.type _ _) \; sndF) <$> hh = (G1 <$> hh).
  intros.
  unfold fsplitter.
  simpl; auto.
Defined. 

Lemma fsplitter_proj1 (A B C: cat) (F: A ~> B) (G: A ~> C) :
  (fsplitter F G : Functor.type _ _) \; fstF = F.
  have Eq1 : (fsplitter F G : Functor.type _ _) \; fstF =1 F.
  { unfold fsplitter, fstF; intros; simpl; auto. }
  have Key := @functorP _ _ _ _ Eq1.
  apply: Key.
  move=> a1 a2 f.
  assert (F <$> f = ((fsplitter F G: Functor.type _ _) \; fstF) <$> f) as E.
  { rewrite mediating_fun_ext_proj1; auto. }
  rewrite E.
  simpl.
  move: (funext Eq1); intros.
  dependent destruction funext.
  auto.
Defined.

Lemma fsplitter_proj2 (A B C: cat) (F: A ~> B) (G: A ~> C) :
  (fsplitter F G : Functor.type _ _) \; sndF = G.
  have Eq1 : (fsplitter F G : Functor.type _ _) \; sndF =1 G.
  { unfold fsplitter, sndF; intros; simpl; auto. }
  have Key := @functorP _ _ _ _ Eq1.
  apply: Key.
  move=> a1 a2 f.
  assert (G <$> f = ((fsplitter F G: Functor.type _ _) \; sndF) <$> f) as E.
  { rewrite mediating_fun_ext_proj2; auto. }
  rewrite E.
  simpl.
  move: (funext Eq1); intros.
  dependent destruction funext.
  auto.
Defined.

Program Definition mediating_fun' (A B C D: cat)
  (F1: A ~> B) (G1: A ~> C) (F2: B ~> D) (G2: C ~> D)
  (e: F1 \; F2 = G1 \; G2) : A -> (ptype F2 G2 : cat).
  intro X.
  exists (fsplitter F1 G1 X); simpl.
  assert (F2 (F1 X) = (F1 \; F2) X) as H.
  { auto. }
  rewrite H.
  rewrite e; auto. 
Defined.  

Program Definition mediating_fun_prop (A B C D: cat)
  (F1: A ~> B) (G1: A ~> C) (F2: B ~> D) (G2: C ~> D)
  (e: F1 \; F2 = G1 \; G2) (X: A) :
  F2 (F1 X) = G2 (G1 X).
  assert (F2 (F1 X) = (F1 \; F2) X) as H.
  { auto. }
  rewrite H.
  rewrite e; auto. 
Qed.  
  
Program Definition mediating_fun (A B C D: cat)
  (F1: A ~> B) (G1: A ~> C) (F2: B ~> D) (G2: C ~> D)
  (e: F1 \; F2 = G1 \; G2) : A -> (ptype F2 G2 : cat).
  intro X.
  exists (fsplitter F1 G1 X); simpl.
  eapply mediating_fun_prop; eauto.
Defined.

Lemma Fhom_comp (A B C: cat)
  (F1: A ~> B) (F2: B ~> C) (x y: obj A) (m: x ~> y) :
  (F1 \; F2) <$> m = F2 <$> (F1 <$> m).
  auto.
Defined.

Lemma Fhom_comp' (A B C: cat)
  (F1: A ~> B) (F2: B ~> C) (x y: obj A) (m: x ~> y) :
  @Fhom A C (F1 \; F2) x y m =
  @Fhom B C F2 (F1 x) (F1 y) (@Fhom A B F1 x y m).
  auto.
Defined.

Lemma prefunctorPcast_inv
  (C D : quiver) (F G : C ~> D) (eqFG : F =1 G) :
  (forall a b f,
      F = G ->  
     ecast2 x y (x ~> y) (eqFG a) (eqFG b) (F <$> f) = G <$> f).
(* ecast x (x ~> G b) (eqFG a) (ecast y (F a ~> y) (eqFG b) (F <$> f)) =
  G <$> f *)
Proof.
  intros a b f H.
  dependent destruction H.
  destruct F.
  simpl.
  simpl in *.
  Locate "=1".
  unfold eqfun in *.
  destruct class as [X].
  simpl; simpl in *.
  unfold Fhom.
  simpl.
  destruct X; simpl.
  move: (eqFG a).
  move: (eqFG b).
  intros.
  dependent destruction eqFG0.
  dependent destruction eqFG1.
  auto.
Defined.  

Lemma fstF_ext (C D E : cat) (F : C ~> E) (G : D ~> E)
  (a b : ptype F G) (f : tag a ~> tag b) :   
  F <$> f.1 = (fstF \; F) <$> f.
  unfold fstF.
  unfold fst0.
  unfold comp; simpl.
  unfold fst; simpl.
  unfold ssrfun.comp.
  unfold Fhom.
  destruct f.
  simpl in *; simpl.
  unfold Fhom; simpl.
  auto.
Defined.

Lemma sndF_ext (C D E : cat) (F : C ~> E) (G : D ~> E)
  (a b : ptype F G) (f : tag a ~> tag b) :   
  G <$> f.2 = (sndF \; G) <$> f.
  unfold sndF.
  unfold snd0.
  unfold comp; simpl.
  unfold snd; simpl.
  unfold ssrfun.comp.
  unfold Fhom.
  destruct f.
  simpl in *; simpl.
  unfold Fhom; simpl.
  auto.
Defined.

Lemma prefunctorPcast_transl (C D E : cat) (F : C ~> E) (G : D ~> E)
  (a b : ptype F G) (f : tag a ~> tag b) :
  ecast2 x y (x ~> y) (tagged a) (tagged b) (@Fhom _ _ (fstF \; F) _ _ f) =
  ecast2 x y (x ~> y) (tagged a) (tagged b) (F <$> f.1). 
  simpl.
  rewrite fstF_ext. auto.
Qed.

Lemma mediating_morph_prefunctor_prop (A B C D: cat)
  (F1: A ~> B) (G1: A ~> C) (F2: B ~> D) (G2: C ~> D)
  (e: F1 \; F2 = G1 \; G2)
  (a1 a2 : A)
  (hh : a1 ~> a2) :
  ecast x (x ~> G2 (tag (mediating_fun e a2)).2) (tagged (mediating_fun e a1))
    (ecast y (F2 (tag (mediating_fun e a1)).1 ~> y)
       (tagged (mediating_fun e a2)) (F2 <$> (fsplitter F1 G1 <$> hh).1)) =
  G2 <$> (fsplitter F1 G1 <$> hh).2.
  have ->: (fsplitter F1 G1 <$> hh).2 = G1 <$> hh.
  { unfold fsplitter; simpl; auto. }

  have ->: G2 <$> G1 <$> hh = (G1 \; G2) <$> hh.
  { auto. }

  have ->: (fsplitter F1 G1 <$> hh).1 = F1 <$> hh.
  { unfold fsplitter; simpl; auto. }
  
  have ->: F2 <$> F1 <$> hh = (F1 \; F2) <$> hh.
  { auto. }

  assert (F1 \; F2 =1 G1 \; G2) as eqFG.
  { unfold eqfun.
    intros.
    rewrite e; auto.
  }  

  move: (tagged (mediating_fun e a1)).
  intros tagged1.

  move: (tagged (mediating_fun e a2)).
  intros tagged2.

  simpl in tagged1.
  simpl in tagged2.
  simpl.
  
  have U := (@prefunctorPcast_inv _ _ _ _ eqFG a1 a2 hh).

  have H : (tagged1 = eqFG a1).
  { eapply Prop_irrelevance. }
  have H0 : (tagged2 = eqFG a2).
  { eapply Prop_irrelevance. }

  inversion H; subst.
  clear H1.

  eapply U; eauto.
  rewrite e.
  reflexivity.
Defined.  

Lemma mediating_morph_prefunctor (A B C D: cat)
  (F1: A ~> B) (G1: A ~> C) (F2: B ~> D) (G2: C ~> D)
  (e: F1 \; F2 = G1 \; G2) :
  IsPreFunctor A (ptype F2 G2) (mediating_fun e).
  econstructor; eauto.
  intros a1 a2 hh.

  exists (fsplitter F1 G1 <$> hh). 

  eapply mediating_morph_prefunctor_prop; eauto.
Defined.  

HB.instance Definition mediating_morph_PreFunctor (A B C D: cat)
  (F1: A ~> B) (G1: A ~> C) (F2: B ~> D) (G2: C ~> D)
  (e: F1 \; F2 = G1 \; G2) : 
  IsPreFunctor A (ptype F2 G2) (mediating_fun e) :=
  mediating_morph_prefunctor e.

Lemma mediating_morph_eq_proj1 (A B C D: cat)
  (F1: A ~> B) (G1: A ~> C) (F2: B ~> D) (G2: C ~> D)
  (e: F1 \; F2 = G1 \; G2) :
  F1 \; F2 = (fsplitter F1 G1: Functor.type _ _) \; fstF \; F2.
  rewrite compoA.
  rewrite fsplitter_proj1.
  auto.
Qed.

Lemma mediating_morph_eq_proj2 (A B C D: cat)
  (F1: A ~> B) (G1: A ~> C) (F2: B ~> D) (G2: C ~> D)
  (e: F1 \; F2 = G1 \; G2) :
  G1 \; G2 = (fsplitter F1 G1: Functor.type _ _) \; sndF \; G2.
  rewrite compoA.
  rewrite fsplitter_proj2.
  auto.
Qed.

Lemma mediating_morph_functor (A B C T : cat)
  (l2t : A ~> T)
  (r2t : B ~> T)
  (b2l : C ~> A)
  (b2r : C ~> B)
  (sq : b2l \; l2t = b2r \; r2t) :
  C ~> ptype l2t r2t.
  unfold ptype.  
  econstructor; eauto.
  econstructor; eauto.
  instantiate (2:= @mediating_fun C A B T b2l b2r l2t r2t sq).
  instantiate (1:= mediating_morph_PreFunctor sq).
  econstructor; eauto.
  { intros.
    unfold mediating_fun; simpl.

    unfold idmap at 2; simpl.
    unfold Fhom; simpl.
   
    have E1 : (fsplitter b2l b2r <$> idmap = idmap).
    { intros. rewrite F1; auto. }
    specialize (E1 a).

    move: (mediating_morph_prefunctor_prop sq idmap).
    intro mP.
    move: mP.
  
    rewrite E1.
    intros.
    simpl in *; simpl.
    unfold idmap_psubdef.
    simpl.
    unfold Tagged; simpl.

    eapply (eq_existT_curried eq_refl); simpl.
    eapply Prop_irrelevance.
  }
  { intros.
    unfold mediating_fun; simpl.

    unfold comp at 2; simpl.

    have E1: (fsplitter b2l b2r <$> (f \; g) =
                ((fsplitter b2l b2r <$> f) \; (fsplitter b2l b2r <$> g))). 
    { rewrite Fcomp; eauto. }

    unfold comp_psubdef; simpl.
    unfold Tagged; simpl.
    
    unfold Fhom at 1; simpl.
  
    move: (mediating_morph_prefunctor_prop sq (f \; g)).
    intro mPfg.

    move: (commaE.comp_psubdef_obligation_1 _ _).
    simpl; intro.

    eapply (eq_existT_curried E1); simpl.

    eapply Prop_irrelevance.
  }
Defined.  

Lemma mediating_prepullback_morph (A B : cat)
  (csp0 : cospan A B)
  (pp : prepullback csp0) : pp ~> pbk csp0.  
  destruct pp as [sp1 class].
  destruct class as [X].
  destruct X.
  destruct csp0 as [T l2t r2t] ; simpl in *.
  destruct sp1 as [C b2l b2r]; simpl in *.
  exists (mediating_morph_functor is_square).
  {
    unfold comp; simpl.

    assert ((pcat_prj1 \o mediating_fun is_square)%FUN =1 b2l) as eqFG.
    { intro; simpl; auto. }

    eapply functorPcast.
    instantiate (1:=eqFG).
    simpl; intros.
  
    unfold mediating_morph_functor.
    unfold mediating_fun.
    unfold pcat_prj1; simpl.
    unfold fsplitter; simpl.
    unfold tag.
    simpl.
    unfold ssrfun.comp; simpl.
  
    move: (eqFG a).
    intro.
    move: (eqFG b).
    intro.
    clear eqFG.
    unfold ssrfun.comp in *.
    unfold pcat_prj1 in *.
    unfold tag in *.
    simpl in *.

    dependent destruction eqFG0.
    dependent destruction eqFG1.
    auto.
  }
  { unfold comp; simpl.

    assert ((pcat_prj2 \o mediating_fun is_square)%FUN =1 b2r) as eqFG.
    { intro; simpl; auto. }

    eapply functorPcast.
    instantiate (1:=eqFG).
    simpl; intros.
  
    unfold mediating_morph_functor.
    unfold mediating_fun.
    unfold pcat_prj2; simpl.
    unfold fsplitter; simpl.
    unfold tag.
    simpl.
    unfold ssrfun.comp; simpl.
  
    move: (eqFG a).
    intro.
    move: (eqFG b).
    intro.
    clear eqFG.
    unfold ssrfun.comp in *.
    unfold pcat_prj2 in *.
    unfold tag in *.
    simpl in *.

    dependent destruction eqFG0.
    dependent destruction eqFG1.
    auto.
  }
Defined.  
   
Lemma fsplitter_exchange0 (bot0 A B topK : cat)
  (left2topK : A ~> topK)
  (right2topK : B ~> topK)
  (bot2left0 : bot0 ~> A)
  (bot2right0 : bot0 ~> B)
  (bot_map0 : bot0 ~> ptype left2topK right2topK) :
    bot_map0 \;
      (fsplitter (pcat_prj1: Functor.type _ _) (pcat_prj2: Functor.type _ _) :
        Functor.type _ _) 
    = 
      (fsplitter (bot_map0 \; (pcat_prj1: Functor.type _ _))
         (bot_map0 \; (pcat_prj2: Functor.type _ _)): Functor.type _ _).

  assert (bot_map0 \;
      (fsplitter (pcat_prj1: Functor.type _ _) (pcat_prj2: Functor.type _ _) :
        Functor.type _ _) 
    =1 
      (fsplitter (bot_map0 \; (pcat_prj1: Functor.type _ _))
         (bot_map0 \; (pcat_prj2: Functor.type _ _)): Functor.type _ _))
    as eqFG.
  { auto. }

  simpl; simpl in *.
  eapply functorPcast; eauto.
  instantiate (1:=eqFG).
  simpl; intros.

  revert eqFG.
  
  intros.
  unfold fsplitter; simpl.
  destruct bot_map0; simpl; simpl in *.
  unfold comp; simpl.
  unfold fsplitter; simpl.
  unfold ssrfun.comp; simpl.

  move: (eqFG a).
  intro.
  move: (eqFG b).
  intro.
  unfold Fhom; simpl.
  unfold Fhom; simpl.
  unfold Fhom; simpl.
  move: (pcat_prj1_isPreFunctor_obligation_1 (IsPreFunctor.Fhom class f)).
  intro.
  move: (pcat_prj2_isPreFunctor_obligation_1 (IsPreFunctor.Fhom class f)).
  intro.
  simpl.

  dependent destruction eqFG0.
  dependent destruction eqFG1.
  auto.
Qed.
  
Lemma fsplitter_exchange (bot0 A B topK : cat)
  (left2topK : A ~> topK)
  (right2topK : B ~> topK)
  (bot2left0 : bot0 ~> A)
  (bot2right0 : bot0 ~> B)
  (is_square : bot2left0 \; left2topK = bot2right0 \; right2topK)
  (bot_map0 : bot0 ~> ptype left2topK right2topK)
  (bot2left_map0 : bot_map0 \; (pcat_prj1: Functor.type _ _) = bot2left0)
  (bot2right_map0 : bot_map0 \; (pcat_prj2: Functor.type _ _) = bot2right0) :
    bot_map0 \;
      (fsplitter (pcat_prj1: Functor.type _ _) (pcat_prj2: Functor.type _ _) :
        Functor.type _ _) 
    = 
      (fsplitter (bot2left0: Functor.type _ _)
                 (bot2right0: Functor.type _ _) : Functor.type _ _).

  rewrite -bot2left_map0.
  rewrite -bot2right_map0.
  eapply fsplitter_exchange0; eauto.
Qed.  

Lemma fsplitter_fst_eq (A B topK : cat)
    (left2topK : A ~> topK) (right2topK : B ~> topK) :
  ((fsplitter (pcat_prj1: Functor.type (ptype left2topK right2topK) _)
             (pcat_prj2: Functor.type (ptype left2topK right2topK) _) :
     Functor.type _ _) \; fstF) =
    (pcat_prj1 : Functor.type (ptype left2topK right2topK) _).
  simpl.
  eapply fsplitter_proj1; eauto.
Qed.  

Lemma fsplitter_snd_eq (A B topK : cat)
    (left2topK : A ~> topK) (right2topK : B ~> topK) :
  ((fsplitter (pcat_prj1: Functor.type (ptype left2topK right2topK) _)
             (pcat_prj2: Functor.type (ptype left2topK right2topK) _) :
     Functor.type _ _) \; sndF) =
    (pcat_prj2 : Functor.type (ptype left2topK right2topK) _).
  simpl.
  eapply fsplitter_proj2; eauto.
Qed.  


(***********************************************************************)

Lemma fsplitter_tag_eq (A B topK : cat)
    (left2topK : A ~> topK) (right2topK : B ~> topK) :
  (fsplitter (pcat_prj1: Functor.type (ptype left2topK right2topK) _)
             (pcat_prj2: Functor.type (ptype left2topK right2topK) _) :
     Functor.type _ _) =
    (pcat_tag : Functor.type (ptype left2topK right2topK) _).

  assert ((fsplitter (pcat_prj1: Functor.type (ptype left2topK right2topK) _)
             (pcat_prj2: Functor.type (ptype left2topK right2topK) _) :
     Functor.type _ _) =1
    (pcat_tag : Functor.type (ptype left2topK right2topK) _)) as eqFG.
  { unfold eqfun.
    intro x.
    destruct x as [[a b] E].
    unfold fsplitter, pcat_tag; simpl.
    unfold fsplitter; simpl.
    unfold pcat_prj1, pcat_prj2; simpl.
    auto.
  }
  
  simpl.
  eapply functorPcast.
  instantiate (1:= eqFG).
  intros x1 x2 f.
  destruct x1 as [[a1 b1] E1].
  destruct x2 as [[a2 b2] E2].
  simpl; simpl in *.
   
  unfold fsplitter, pcat_tag; simpl.
  unfold pcat_prj1, pcat_prj2; simpl.
  unfold tag.
  destruct f as [[f1 f2] Ef] ; simpl; simpl in *.

  move: (existT
          (fun f : (a1, b1) ~> (a2, b2) =>
           ecast x (x ~> right2topK b2) E1
             (ecast y (left2topK a1 ~> y) E2 (left2topK <$> f.1)) =
             right2topK <$> f.2) (f1, f2) Ef).
  intro s.

  move: (eqFG
     (existT (fun x : A * B => left2topK x.1 = right2topK x.2) (a1, b1) E1)).
  intro.

  move: (eqFG
          (existT (fun x : A * B => left2topK x.1 = right2topK x.2) (
               a2, b2) E2)).
  intro.

  clear Ef.
  dependent destruction s.
  simpl; simpl in *.
  destruct x.
  simpl; simpl in *.
  unfold fsplitter, pcat_tag in *; simpl in *.
  unfold pcat_prj1, pcat_prj2 in *; simpl in *.

  dependent destruction eqFG0.
  dependent destruction eqFG1.
  simpl.
  auto.
Qed.  

Lemma functor_comp_Fhom (A B C: cat) (F : A ~> B) (G : B ~> C) :
  @Fhom _ _ (F \; G) = fun _ _ f => @Fhom _ _ G _ _ (@Fhom _ _ F _ _ f).

  assert (forall (x y: A) (f: x ~> y),
             @Fhom _ _ (F \; G) _ _ f = @Fhom _ _ G _ _ (@Fhom _ _ F _ _ f)).
  { intros.
    eapply comp_Fun. }
  eapply funext; eauto.
Qed.  
  
Lemma tag_functor_comp_Fhom (bot0 A B topK : cat)
    (left2topK : A ~> topK) (right2topK : B ~> topK)
    (g1 : bot0 ~> ptype left2topK right2topK) :
  @Fhom _ _ (g1 \; (pcat_tag: Functor.type _ _)) =
    fun _ _ f => tag (@Fhom _ _ g1 _ _ f).
  
 assert (@Fhom _ _ (g1 \; (pcat_tag: Functor.type _ _)) =
           fun _ _ f => @Fhom _ _ pcat_tag _ _ (@Fhom _ _ g1 _ _ f)) as V.
 eapply functor_comp_Fhom; eauto.
 auto.
Qed.

Lemma tag_functor_comp_Fhom0 (bot0 A B topK : cat)
    (left2topK : A ~> topK) (right2topK : B ~> topK)
    (g1 : bot0 ~> ptype left2topK right2topK) (a1 a2: bot0) :
  @Fhom _ _ (g1 \; (pcat_tag: Functor.type _ _)) a1 a2 =
    fun (f: a1 ~> a2) => tag (@Fhom _ _ g1 a1 a2 f).
  
 assert (@Fhom _ _ (g1 \; (pcat_tag: Functor.type _ _)) =
           fun _ _ f => @Fhom _ _ pcat_tag _ _ (@Fhom _ _ g1 _ _ f)) as V.
 eapply functor_comp_Fhom; eauto.
 auto.
Qed.

Lemma tag_functor_Fhom_eq (bot0 A B topK : cat)
    (left2topK : A ~> topK) (right2topK : B ~> topK)
    (g1 g2 : bot0 ~> ptype left2topK right2topK)
    (et: forall x, tag (g1 x) = tag (g2 x))
    (ef: forall x, g1 x = g2 x)
    (a1 a2: bot0) (f: a1 ~> a2) :
  (ecast2 x y (x ~> y) (et a1) (et a2) (tag (@Fhom _ _ g1 _ _ f)) =
     tag (@Fhom _ _ g2 _ _ f)) ->
  (ecast2 x y (x ~> y) (ef a1) (ef a2) (@Fhom _ _ g1 _ _ f) =
     @Fhom _ _ g2 _ _ f).
  intros.
  destruct g1 as [m1 [R1 S1]].
  destruct g2 as [m2 [R2 S2]].
  simpl; simpl in *.
  assert (m1 = m2) as K.
  { eapply funext; eauto. }
  inversion K; subst.
  clear H0.

  revert H.
  move: (et a1).
  intro.
  move: (et a2).
  intro.
  move: (ef a1).
  intro.
  move: (ef a2).
  intro.

  dependent destruction et0.
  dependent destruction et1.
  dependent destruction ef0.
  dependent destruction ef1.
  clear et.
  clear ef.

  simpl; intros; simpl in *.
  unfold tag in H.
  simpl in *.

  revert H.
  move: ({|
       Functor.sort := m2;
       Functor.class :=
         {|
           Functor.cat_IsPreFunctor_mixin := R1;
           Functor.cat_PreFunctor_IsFunctor_mixin := S1
         |}
     |} <$> f).
  move: ({|
       Functor.sort := m2;
       Functor.class :=
         {|
           Functor.cat_IsPreFunctor_mixin := R2;
           Functor.cat_PreFunctor_IsFunctor_mixin := S2
         |}
          |} <$> f).
  intros.
  destruct Fhom.
  destruct Fhom0.
  simpl; simpl in *.
  inversion H; subst.
  clear H0.
  f_equal.
  eapply Prop_irrelevance.
Qed.  

(** fsplitter is mono *)
Lemma fsplitter_mono (A B topK : cat)
  (left2topK : A ~> topK) (right2topK : B ~> topK)
  (bot0: cat)
    (g1 g2 : bot0 ~> ptype left2topK right2topK) :
  g1 \; (fsplitter (pcat_prj1: Functor.type _ _)
           (pcat_prj2: Functor.type _ _) : Functor.type _ _) =
  g2 \; (fsplitter (pcat_prj1: Functor.type _ _)
           (pcat_prj2: Functor.type _ _) : Functor.type _ _) ->
  g1 = g2.

  rewrite fsplitter_tag_eq.  
  intros.
  
  assert (g1 =1 g2) as eqFG.
  { unfold eqfun.
    intros.
    inversion H; subst.
    unfold pcat_tag in H1; simpl in *.
    unfold ssrfun.comp in H1; simpl in *.
    unfold pcat_prj1, pcat_prj2 in *; simpl in *.
  
    destruct g1.
    destruct g2.
    simpl in *; simpl.
    clear H2.

    assert (forall x : bot0, ((tag (sort x)).1, (tag (sort x)).2) =
                             ((tag (sort0 x)).1, (tag (sort0 x)).2)) as H0.
    { eapply funext_equal_f; eauto. }
    specialize (H0 x).
  
    clear H1.
    revert H0.
    move: (sort x).
    intro.
    move: (sort0 x).
    intro.
    destruct sort1.
    destruct sort2.
    destruct x0.
    destruct x1.
    simpl.
    intros.
    inversion H0; subst.
    clear H0.
    f_equal.
    eapply Prop_irrelevance.
  }
 
  eapply functorPcast.
  intros.
  instantiate (1:=eqFG).

  simpl in *; simpl.
  unfold eqfun in eqFG.

  assert (forall x : bot0, tag (g1 x) = tag (g2 x)) as eT.
  { intros. rewrite eqFG. auto. }

  eapply tag_functor_Fhom_eq.
  instantiate (1:=eT).

  destruct g1 as [m1 [R1 S1]].
  destruct g2 as [m2 [R2 S2]].
  simpl in *; simpl.

  assert (m1 = m2) as E.
  { eapply funext; eauto. }

  inversion E; subst.
  clear H0.

  move: (eT a).
  intro.
  move: (eT b).
  intro.
  dependent destruction eT0.
  dependent destruction eT1.
  clear eT.
  clear eqFG.

  revert f.
  eapply funext_equal_f.
  rewrite -tag_functor_comp_Fhom0.
  rewrite -tag_functor_comp_Fhom0.

  inversion H; subst.
  dependent destruction H1; eauto.

  unfold Fhom; simpl.

  eapply equal_f_dep in x.
  instantiate (1:= a) in x.
  eapply equal_f_dep in x.
  instantiate (1:=b) in x.
  auto.
Qed.

Lemma fsplitter_mono1 (A B topK : cat)
  (left2topK : A ~> topK) (right2topK : B ~> topK) :
  forall (bot0: cat)
    (g1 g2 : bot0 ~> ptype left2topK right2topK),
  g1 \; (fsplitter (pcat_prj1: Functor.type _ _)
           (pcat_prj2: Functor.type _ _) : Functor.type _ _) =
  g2 \; (fsplitter (pcat_prj1: Functor.type _ _)
           (pcat_prj2: Functor.type _ _) : Functor.type _ _) ->
  g1 = g2.
intros. eapply fsplitter_mono; eauto.
Qed.

(** unicity of the mediating morphism (generic) *)
Lemma cat_unique_med (A B: cat)
    (csp: cospan A B) (ppb : prepullback csp) :
  forall (ppbM0 ppbM1 : ppb ~> pbk csp),
    ppbM0 = ppbM1.
  intros.
  
  destruct ppb as [sp0 class0].
  destruct class0 as [X0].
  destruct X0.
  simpl in *; simpl.

  set botK := bot (pbk csp).
  set bot2leftK := bot2left (pbk csp).
  set bot2rightK := bot2right (pbk csp).
  
  destruct sp0 as [bot0 bot2left0 bot2right0].
  simpl; simpl in *.

  destruct csp as [topK left2topK right2topK].
  simpl; simpl in *.
  
  set mon_f := fsplitter bot2leftK bot2rightK. 
  set mon_F: Functor.type _ _ := mon_f. 
  
  destruct ppbM0 as [bot_map0 bot2left_map0 bot2right_map0].
  simpl in *; simpl.
  destruct ppbM1 as [bot_map1 bot2left_map1 bot2right_map1].
  simpl in *; simpl.

  set path0 := bot_map0 \; mon_F.
  set path1 := bot_map1 \; mon_F.

  assert (path0 = bot_map0 \;
                (fsplitter bot2leftK bot2rightK : Functor.type _ _)) as E0.
  { auto. }

  assert (path1 = bot_map1 \;
                (fsplitter bot2leftK bot2rightK : Functor.type _ _)) as E1.
  { auto. }

  assert (path0 = path1) as E2.
  { subst bot2leftK bot2rightK.
    rewrite E0.
    rewrite E1.
    simpl; simpl in *.
    rewrite (@fsplitter_exchange bot0 A B topK left2topK right2topK
               bot2left0 bot2right0); eauto.
    rewrite (@fsplitter_exchange bot0 A B topK left2topK right2topK
               bot2left0 bot2right0); eauto.
  }  
  subst mon_F.
  subst mon_f.

  set monoP := (@fsplitter_mono1 A B topK left2topK right2topK).
  
  specialize (monoP bot0 bot_map0 bot_map1).
  eapply monoP in E2.
  inversion E2; subst.
  f_equal.
  eapply Prop_irrelevance.
  eapply Prop_irrelevance.
Qed.
   
Lemma cat_pb :
   forall (a b: cat) (c: cospan a b),
     prepullback_isTerminal cat a b c (pbk c).
  intros.
  econstructor; eauto.
  set abs_med_funX := @mediating_prepullback_morph a b c.  
  econstructor; eauto.
  (* ppb0M is a fresh prepullback morphism from ppb0 to pbk *)
  intros ppb0 ppb0M.
  instantiate (1:=abs_med_funX).
  set med_funX := abs_med_funX ppb0.
  eapply cat_unique_med; eauto.
Qed.  

(* Cat has all pullbacks *)
HB.instance Definition _ (a b: cat) (c: cospan a b) := @cat_pb a b c.


(*
Fail HB.instance Definition fsplitter_IsMono (bot0 A B topK : cat)
    (left2topK : A ~> topK) (right2topK : B ~> topK)
    (g1 g2 : bot0 ~> ptype left2topK right2topK) :
  @IsMono cat _ _ (fsplitter (pcat_prj1: Functor.type _ _)
                     (pcat_prj2: Functor.type _ _) :
      Functor.type _ _) :=
  @IsMono.Build cat _ _ (fsplitter (pcat_prj1: Functor.type _ _)
                     (pcat_prj2: Functor.type _ _) :
      Functor.type _ _)            
  (@fsplitter_mono1 A B topK left2topK right2topK).          
*)

(************************************************************************)
(*
Definition splitter (A: cat) : A -> ((A * A)%type : cat) := fun x => (x, x).

Program Definition splitter_Fhom (A: cat) :
  forall (a b : A), (a ~> b) -> (splitter a ~> splitter b).
intros.
unfold splitter.
unfold hom; simpl.
unfold prod_hom_subdef; simpl.
exact (X, X).
Defined.

Lemma splitter_IsPreFunctor_lemma (A: cat) :
  IsPreFunctor A ((A * A)%type : cat) (@splitter A).
  econstructor; eauto.
  intros.
  unfold splitter, hom; simpl.
  unfold prod_hom_subdef; simpl.
  exact (H, H).
Defined.  
  
HB.instance Definition splitter_IsPreFunctor (A: cat) :=
  splitter_IsPreFunctor_lemma A.

Lemma splitter_IsFunctor_lemma (A: cat) :
  PreFunctor_IsFunctor A ((A * A)%type : cat) (@splitter A).
  econstructor; eauto.
Defined.

HB.instance Definition splitter_IsFunctor (A: cat) :=
  splitter_IsFunctor_lemma A.

Program Definition splitter_morph (A: cat) : A ~> ((A * A)%type : cat).
unfold hom; simpl.
exact (@splitter A). 
Defined.
*)

(*
Definition joiner (A B C: cat) (F: A ~> C) (G: B ~> C) 
  (e: forall x: A * B, F (x.1) = G (x.2)) :
  ((A * B)%type : cat) -> (ptype F G : cat) :=
  fun ab => existT (fun x : A * B => F x.1 = G x.2) ab (e ab).
                                      
Program Definition joiner1 (A B C: cat) (F: A ~> C) (G: B ~> C) 
  (e: fstF \; F = sndF \; G) :
  ((A * B)%type : cat) -> (ptype F G : cat).
intro ab.
exists ab.
dependent destruction e.
eapply funext_equal_f in x0; eauto.
Defined.  
*)
(*
Lemma lower_eq (A B C : cat)
  (F: A ~> C) (G: B ~> C)
  (e: @fstF A B \; F = @sndF A B \; G) :
  forall x: A * B, F (x.1) = G (x.2).
  intros.
  destruct F.
  destruct G.
  unfold fstF, sndF in *.
  unfold comp in *.
  simpl; simpl in *.
  dependent destruction e.
  unfold ssrfun.comp in x; simpl in x.
  eapply funext_equal_f in x; eauto.
Qed.  

Lemma cond_joiner_IsPreFunctor_lemma (A B C : cat)
  (F: A ~> C) (G: B ~> C)
  (e: @fstF A B \; F = @sndF A B \; G) :
  IsPreFunctor (A * B)%type (ptype F G) (joiner (lower_eq e)).
  unfold joiner; simpl.
  econstructor; eauto.
  intros ab1 ab2 fg.
  exists fg.

  set F1 := (@fstF A B \; F).
  set G1 := (@sndF A B \; G).  
 
  assert (F1 =1 G1) as eqFG1.
  { subst F1 G1.
    unfold eqfun.
    intros.
    unfold fstF, sndF.
    simpl.
    unfold fstF, sndF in e.
    unfold fst0, snd0 in *.
    unfold comp in *.
    simpl in *.
    destruct F.
    destruct G.
    simpl in *.
    inversion e; subst.
    unfold ssrfun.comp in H0; simpl in H0.
    eapply funext_equal_f in H0; eauto.
  }  
  
  assert (F1 = G1) as eqFG2.
  { auto. } 

  assert (ecast x (x ~> G1 ab2) (eqFG1 ab1)
        (ecast y (F1 ab1 ~> y) (eqFG1 ab2) (F1 <$> fg)) = (G1 <$> fg)) as Eh.
  { eapply prefunctorPcast_inv; eauto.
    f_equal; auto. }

  subst F1 G1.
  unfold sndF in *.
  simpl in *.
  unfold snd0 in *; simpl in *.
  unfold Fhom in Eh; simpl in *.
  unfold Fhom in Eh; simpl in *.
  unfold Fhom; simpl.
  rewrite -Eh.

  assert ((lower_eq e ab1) = (eqFG1 ab1)) as A1.
  { eapply Prop_irrelevance. }
  rewrite A1.

  assert ((lower_eq e ab2) = (eqFG1 ab2)) as A2.
  { eapply Prop_irrelevance. }
  rewrite A2.

  auto.
Defined.
 *)

(*
Lemma mediating_morph_prefunctor' (A B C D: cat)
  (F1: A ~> B) (G1: A ~> C) (F2: B ~> D) (G2: C ~> D)
  (e: F1 \; F2 = G1 \; G2) :
  IsPreFunctor A (ptype F2 G2) (mediating_fun e).
  econstructor; eauto.
  intros a1 a2 hh.

  exists (fsplitter F1 G1 <$> hh).

  have ->: (fsplitter F1 G1 <$> hh).2 = G1 <$> hh.
  { unfold fsplitter; simpl; auto. }

  have ->: G2 <$> G1 <$> hh = (G1 \; G2) <$> hh.
  { auto. }

  have ->: (fsplitter F1 G1 <$> hh).1 = F1 <$> hh.
  { unfold fsplitter; simpl; auto. }
  
  have ->: F2 <$> F1 <$> hh = (F1 \; F2) <$> hh.
  { auto. }

  assert (F1 \; F2 =1 G1 \; G2) as eqFG.
  { unfold eqfun.
    intros.
    rewrite e; auto.
  }  

  move: (tagged (mediating_fun e a1)).
  intros tagged1.

  move: (tagged (mediating_fun e a2)).
  intros tagged2.

  simpl in tagged1.
  simpl in tagged2.
  
  set U := (@prefunctorPcast_inv _ _ _ _ eqFG a1 a2 hh).

  move: U.
  intro U.

  assert (ecast x (x ~> (G1 \; G2) a2) (eqFG a1)
       (ecast y ((F1 \; F2) a1 ~> y) (eqFG a2) ((F1 \; F2) <$> hh)) =
           (G1 \; G2) <$> hh) as W.
  { eapply U; auto.
    rewrite e; auto.
  }  
    
  assert (tagged1 = eqFG a1).
  { eapply Prop_irrelevance. }

  inversion H; subst.
  clear H0.

  assert (tagged2 = eqFG a2).
  { eapply Prop_irrelevance. }

  inversion H; subst.
  clear H0.
  simpl.
  simpl in W.
  auto.
Defined.
*)

(************************************************************************)
(*
Program Definition brel_fcast {X Y C : Type} {F: X -> C} {G: Y -> C}
  {a1 b1: X} {a2 b2: Y} {R: C -> C -> Type}
  (e1: F a1 = G a2) (e2: F b1 = G b2) :
  R (G a2) (G b2) = R (F a1) (F b1).
rewrite e1.
rewrite e2.
reflexivity.
Defined.

Program Definition recast2 {X Y C : Type} {F: X -> C} {G: Y -> C}
  {a1 b1: X} {a2 b2: Y} {R: C -> C -> Type}
  (e1: F a1 = G a2) (e2: F b1 = G b2) 
  (x: R (G a2) (G b2)) : R (F a1) (F b1).
rewrite -(brel_fcast e1 e2).
exact x.
Defined.

Program Definition brel_fcast_h {X Y C : Type} {F: X -> C} {G: Y -> C}
  {a1 b1: X} {a2 b2: Y} {R: C -> C -> Type}
  (e1: F a1 = G a2) (e2: F b1 = G b2) 
  (x: R (G a2) (G b2)) (P: forall T: Type, T -> Prop) :
  P _ x = P _ (recast2 e1 e2 x).
unfold recast2.
unfold eq_rect.
unfold brel_fcast.
unfold eq_ind_r.
unfold eq_ind.
unfold eq_sym.
destruct e1.
destruct e2.
auto.
Defined.

Program Definition brel_fcast_3h {X Y C : Type} {F: X -> C} {G: Y -> C}
  {a1 b1 c1: X} {a2 b2 c2: Y} {R: C -> C -> Type}
  (e1: F a1 = G a2) (e2: F b1 = G b2) (e3: F c1 = G c2) 
  (x: R (G a2) (G b2)) (y: R (G b2) (G c2)) (z: R (G a2) (G c2))
  (P: forall T1 T2 T3: Type, T1 -> T2 -> T3 -> Prop) :
  P _ _ _ x y z = P _ _ _ (recast2 e1 e2 x) (recast2 e2 e3 y) (recast2 e1 e3 z).
unfold recast2.
unfold eq_rect.
unfold brel_fcast.
unfold eq_ind_r.
unfold eq_ind.
unfold eq_sym.
destruct e1.
destruct e2.
destruct e3.
auto.
Defined.

Program Definition brel_fcast_3hh {X Y C : Type} {F: X -> C} {G: Y -> C}
  {a1 b1 c1: X} {a2 b2 c2: Y} {R: C -> C -> Type}
  (e1: F a1 = G a2) (e2: F b1 = G b2) (e3: F c1 = G c2) 
  (x: R (G a2) (G b2)) (y: R (G b2) (G c2)) (z: R (G a2) (G c2))
  (P: forall (d1 d2 d3: C), R d1 d2 -> R d2 d3 -> R d1 d3 -> Prop) :
  P _ _ _ x y z = P _ _ _ (recast2 e1 e2 x) (recast2 e2 e3 y) (recast2 e1 e3 z).
unfold recast2.
unfold eq_rect.
unfold brel_fcast.
unfold eq_ind_r.
unfold eq_ind.
unfold eq_sym.
destruct e1.
destruct e2.
destruct e3.
auto.
Defined.

Program Definition recast2_h {X Y C : Type} {F: X -> C} {G: Y -> C}
  {a1 b1: X} {a2 b2: Y} {R: C -> C -> Type}
  (e1: F a1 = G a2) (e2: F b1 = G b2) 
  (x: R (G a2) (G b2)) (P: forall T: Type, T -> Prop)
  (p: P _ x) : P _ (recast2 e1 e2 x).
rewrite -(brel_fcast_h e1 e2).
exact p.
Defined.

Program Definition recast2_3h {X Y C : Type} {F: X -> C} {G: Y -> C}
  {a1 b1 c1: X} {a2 b2 c2: Y} {R: C -> C -> Type}
  (e1: F a1 = G a2) (e2: F b1 = G b2) (e3: F c1 = G c2) 
  (x: R (G a2) (G b2)) (y: R (G b2) (G c2)) (z: R (G a2) (G c2))
  (P: forall T1 T2 T3: Type, T1 -> T2 -> T3 -> Prop) 
  (p: P _ _ _ x y z) :
    P _ _ _ (recast2 e1 e2 x) (recast2 e2 e3 y) (recast2 e1 e3 z).
rewrite -(brel_fcast_3h e1 e2 e3).
exact p.
Defined.

Program Definition recast2_3hh {X Y C : Type} {F: X -> C} {G: Y -> C}
  {a1 b1 c1: X} {a2 b2 c2: Y} {R: C -> C -> Type}
  (e1: F a1 = G a2) (e2: F b1 = G b2) (e3: F c1 = G c2) 
  (x: R (G a2) (G b2)) (y: R (G b2) (G c2)) (z: R (G a2) (G c2))
  (P: forall (d1 d2 d3: C), R d1 d2 -> R d2 d3 -> R d1 d3 -> Prop) 
  (p: P _ _ _ x y z) :
    P _ _ _ (recast2 e1 e2 x) (recast2 e2 e3 y) (recast2 e1 e3 z).
rewrite -(brel_fcast_3hh e1 e2 e3).
exact p.
Defined.

Program Definition recast_hom {X Y C : precat} {F: X -> C} {G: Y -> C}
  {a1 b1: X} {a2 b2: Y} {R: C -> C -> Type}
  (e1: F a1 = G a2) (e2: F b1 = G b2) 
  (x: (G a2) ~> (G b2)) : (F a1) ~> (F b1).
eapply recast2; eauto.
Defined.

Definition recast21 {X Y C : Type} {F: X -> C} {G: Y -> C}
  {R: C -> C -> Type} {a b: (X * Y)}
  (e: (F (fst a), F (fst b)) = (G (snd a), G (snd b))) 
(* (e1: F (fst a) = G (snd a)) (e2: F (fst b) = G (snd b)) *) 
  (x: R (G (snd a)) (G (snd b))) : R (F (fst a)) (F (fst b)).
  destruct a as [a1 a2].
  destruct b as [b1 b2].
  inversion e; subst.
  rewrite H0.
  rewrite H1.
  auto.
Defined.

Definition mk_pair_eq {X Y C: Type} {F: X -> C} {G: Y -> C} {a b: (X * Y)}
  (e1: F (fst a) = G (snd a)) (e2: F (fst b) = G (snd b)) :
  (F (fst a), F (fst b)) = (G (snd a), G (snd b)).
  destruct a as [a1 a2].
  destruct b as [b1 b2].
  simpl in *; simpl.
  rewrite e1.
  rewrite e2.
  auto.
Defined.  
*)

