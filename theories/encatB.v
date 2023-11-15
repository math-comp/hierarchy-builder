Require Import ssreflect ssrfun.
From HB Require Import structures.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Add Search Blacklist "__canonical__".

Declare Scope algebra_scope.
Delimit Scope algebra_scope with A.
Local Open Scope algebra_scope.

Declare Scope cat_scope.
Delimit Scope cat_scope with cat.
Local Open Scope cat_scope.

(* we assume a few axioms to make life easier *)
Axiom funext : forall {T : Type} {U : T -> Type} [f g : forall t, U t],
  (forall t, f t = g t) -> f = g.
Axiom propext : forall P Q : Prop, P <-> Q -> P = Q.
Axiom Prop_irrelevance : forall (P : Prop) (x y : P), x = y.

(* Shortcut *)
Notation U := Type.

(* Base definition : raw categories = quivers *)
HB.mixin Record IsQuiver C := { hom : C -> C -> U }.
Unset Universe Checking.
#[short(type="quiver")]
HB.structure Definition Quiver : Set := { C of IsQuiver C }.
Set Universe Checking.

Bind Scope cat_scope with quiver.
Bind Scope cat_scope with hom.
Arguments hom {C} : rename.
Notation homs T := (@hom T _ _).
Notation "a ~> b" := (hom a b)
   (at level 99, b at level 200, format "a  ~>  b") : cat_scope.
Notation "a ~>_ C b" := (@hom C a b)
  (at level 99, C at level 0, only parsing) : cat_scope.

(* precategories are quivers + id and comp *)
HB.mixin Record Quiver_IsPreCat C of Quiver C := {
  idmap : forall (a : C), a ~> a;
  comp : forall (a b c : C), (a ~> b) -> (b ~> c) -> (a ~> c);
}.

HB.factory Record IsPreCat C := {
  hom : C -> C -> U;
  idmap : forall (a : C), hom a a;
  comp : forall (a b c : C), hom a b -> hom b c -> hom a c;
}.
HB.builders Context C of IsPreCat C.
  HB.instance Definition _ := IsQuiver.Build C hom.
  HB.instance Definition _ := Quiver_IsPreCat.Build C idmap comp.
HB.end.

Unset Universe Checking.
#[short(type="precat")]
HB.structure Definition PreCat : Set := { C of IsPreCat C }.
Set Universe Checking.

Bind Scope cat_scope with precat.
Arguments idmap {C} {a} : rename.
Arguments comp {C} {a b c} : rename.
Notation "f \o g" := (comp g f) : cat_scope.
Notation "f \; g :> T" := (@comp T _ _ _ f g)
  (at level 60, g, T at level 60, format "f  \;  g  :>  T", only parsing) : cat_scope.
Notation "f \; g" := (comp f g) : cat_scope.
Notation "\idmap_ a" := (@idmap _ a) (only parsing, at level 0) : cat_scope.

(* categories are precategories + laws *)
HB.mixin Record PreCat_IsCat C of PreCat C := {
  comp1o : forall (a b : C) (f : a ~> b), idmap \; f = f;
  compo1 : forall (a b : C) (f : a ~> b), f \; idmap = f;
  compoA : forall (a b c d : C) (f : a ~> b) (g : b ~> c) (h : c ~> d),
    f \; (g \; h) = (f \; g) \; h
}.
Unset Universe Checking.
#[short(type="cat")]
HB.structure Definition Cat : Set := { C of PreCat_IsCat C & IsPreCat C }.
Set Universe Checking.

Bind Scope cat_scope with cat.
Arguments compo1 {C a b} : rename.
Arguments comp1o {C a b} : rename.
Arguments compoA {C a b c d} : rename.

(* the discrete category on a type cannot be the default, we make an alias *)
Definition discrete (T : U) := T.
HB.instance Definition _ T := @IsPreCat.Build (discrete T) (fun x y => x = y)
  (fun=> erefl) (@etrans _).
Lemma etransA T (a b c d : discrete T) (f : a ~> b) (g : b ~> c) (h : c ~> d) :
    f \; (g \; h) = (f \; g) \; h.
Proof. by rewrite /idmap/comp/=; case: _ / h; case: _ / g. Qed.
HB.instance Definition _ T := PreCat_IsCat.Build (discrete T) (@etrans_id _)
   (fun _ _ _ => erefl) (@etransA _).

(* the category of the unit type is the discrete one *)
HB.instance Definition _ := Cat.copy unit (discrete unit).

HB.instance Definition _ := @IsPreCat.Build U (fun A B => A -> B)
  (fun a => idfun) (fun a b c (f : a -> b) (g : b -> c) => (g \o f)%FUN).
HB.instance Definition _ := PreCat_IsCat.Build U (fun _ _ _ => erefl)
  (fun _ _ _ => erefl) (fun _ _ _ _ _ _ _ => erefl).


Lemma Ucomp (X Y Z : U) (f : X ~> Y) (g : Y ~> Z) : f \; g = (g \o f)%FUN.
Proof. by []. Qed.
Lemma Ucompx (X Y Z : U) (f : X ~> Y) (g : Y ~> Z) x : (f \; g) x = g (f x).
Proof. by []. Qed.
Lemma U1 (X : U) : \idmap_X = idfun.
Proof. by []. Qed.
Lemma U1x (X : U) x : \idmap_X x = x.
Proof. by []. Qed.

(* a prefunctor is a functor without laws *)
HB.mixin Record IsPreFunctor (C D : quiver) (F : C -> D) := {
   Fhom : forall (a b : C), (a ~> b) -> (F a ~> F b)
}.

Unset Universe Checking.
HB.structure Definition PreFunctor (C D : quiver) : Set :=
  { F of IsPreFunctor C D F }.
Set Universe Checking.
HB.instance Definition _ := IsQuiver.Build quiver PreFunctor.type.

Notation "F ^$" := (@Fhom _ _ F _ _)
   (at level 1, format "F ^$") : cat_scope.
Notation "F <$> f" := (@Fhom _ _ F _ _ f)
   (at level 58, format "F  <$>  f", right associativity) : cat_scope.

(* prefunctors are equal if their object and hom part are respectively equal *)
Lemma prefunctorP (C D : quiver) (F G : C ~> D) (eqFG : F =1 G) :
   let homF a b F := F a ~> F b in
   (forall a b f, eq_rect _ (homF a b) (F <$> f) _ (funext eqFG) = G <$> f) ->
  F = G.
Proof.
move: F G => [F [[/= Fhom]]] [G [[/= Ghom]]] in eqFG *.
case: _ / (funext eqFG) => /= in Ghom * => eqFGhom.
congr PreFunctor.Pack; congr PreFunctor.Class; congr IsPreFunctor.Axioms_.
by do 3!apply: funext=> ?.
Qed.

(* a functor is a prefunctor + laws for id and comp *)
HB.mixin Record PreFunctor_IsFunctor (C D : precat) (F : C -> D)
     of @PreFunctor C D F := {
   F1 : forall (a : C), F <$> \idmap_a = idmap;
   Fcomp : forall (a b c : C) (f : a ~> b) (g : b ~> c),
      F <$> (f \; g) = F <$> f \; F <$> g;
}.
Unset Universe Checking.

(* precat and cat have a quiver structure *)
HB.structure Definition Functor (C D : precat) : Set :=
  { F of IsPreFunctor C D F & PreFunctor_IsFunctor C D F }.
Set Universe Checking.
HB.instance Definition _ := IsQuiver.Build precat Functor.type.
HB.instance Definition _ := IsQuiver.Build cat Functor.type.

(* functor equality is the same as prefunctor because of PI *)
Lemma functorP (C D : precat) (F G : C ~> D) (eqFG : F =1 G) :
   let homF a b F := F a ~> F b in
   (forall a b f, eq_rect _ (homF a b) (F^$ f) _ (funext eqFG) = G^$ f) ->
  F = G.
Proof.
move=> /= /prefunctorP {eqFG}.
case: F G => [F [/= Fm Fm']] [G [/= Gm Gm']]//=.
move=> [_] /EqdepFacts.eq_sigT_iff_eq_dep eqFG.
case: _ / eqFG in Gm' *.
congr Functor.Pack; congr Functor.Class.
case: Fm' Gm' => [F1 Fc] [G1 Gc].
by congr PreFunctor_IsFunctor.Axioms_; apply: Prop_irrelevance.
Qed.

(* the identity function is a functor *)
HB.instance Definition _ (C : quiver) :=
  IsPreFunctor.Build C C idfun (fun a b => idfun).
HB.instance Definition _ (C : precat) :=
  PreFunctor_IsFunctor.Build C C idfun (fun=> erefl) (fun _ _ _ _ _ => erefl).

(* the composition of prefunctors *)
Section comp_prefunctor.
Context {C D E : quiver} {F : C ~> D} {G : D ~> E}.

HB.instance Definition _ := IsPreFunctor.Build C E (G \o F)%FUN
   (fun a b f => G <$> F <$> f).
Lemma comp_Fun (a b : C) (f : a ~> b) : (G \o F)%FUN <$> f = G <$> (F <$> f).
Proof. by []. Qed.
End comp_prefunctor.

Section comp_functor.
Context {C D E : precat} {F : C ~> D} {G : D ~> E}.
Lemma comp_F1 (a : C) : (G \o F)%FUN <$> \idmap_a = idmap.
Proof. by rewrite !comp_Fun !F1. Qed.
Lemma comp_Fcomp  (a b c : C) (f : a ~> b) (g : b ~> c) :
  (G \o F)%FUN <$> (f \; g) = (G \o F)%FUN <$> f \; (G \o F)%FUN <$> g.
Proof. by rewrite !comp_Fun !Fcomp. Qed.
HB.instance Definition _ := PreFunctor_IsFunctor.Build C E (G \o F)%FUN
   comp_F1 comp_Fcomp.
End comp_functor.

(* precat and cat have a precategory structure *)
HB.instance Definition _ := Quiver_IsPreCat.Build precat
  (fun=> idfun) (fun C D E (F : C ~> D) (G : D ~> E) => (G \o F)%FUN).
HB.instance Definition _ := Quiver_IsPreCat.Build cat
  (fun=> idfun) (fun C D E (F : C ~> D) (G : D ~> E) => (G \o F)%FUN).

Lemma funext_frefl A B (f : A -> B) : funext (frefl f) = erefl.
Proof. exact: Prop_irrelevance. Qed.

(* precategories and categories form a category *)
Definition precat_cat : PreCat_IsCat precat.
Proof.
by split=> [C D F|C D F|C D C' D' F G H];
   apply/functorP => a b f /=; rewrite funext_frefl.
Qed.
HB.instance Definition _ := precat_cat.
Definition cat_cat : PreCat_IsCat cat.
Proof.
by split=> [C D F|C D F|C D C' D' F G H];
   apply/functorP => a b f /=; rewrite funext_frefl.
Qed.
HB.instance Definition _ := cat_cat.

Check (cat : cat).

(* concrete categories *)
HB.mixin Record Quiver_IsPreConcrete T of Quiver T := {
  concrete : T -> U;
  concrete_fun : forall (a b : T), (a ~> b) -> concrete a -> concrete b;
}.
Unset Universe Checking.
#[short(type="preconcrete_quiver")]
HB.structure Definition PreConcreteQuiver : Set :=
  { C of Quiver_IsPreConcrete C & IsQuiver C }.
Set Universe Checking.
Coercion concrete : PreConcreteQuiver.sort >-> Sortclass.

HB.mixin Record PreConcrete_IsConcrete T of PreConcreteQuiver T := {
  concrete_fun_inj : forall (a b : T), injective (concrete_fun a b)
}.
Unset Universe Checking.
#[short(type="concrete_quiver")]
HB.structure Definition ConcreteQuiver : Set :=
  { C of PreConcreteQuiver C & PreConcrete_IsConcrete C }.
Set Universe Checking.

HB.instance Definition _ (C : ConcreteQuiver.type) :=
  IsPreFunctor.Build _ _ (concrete : C -> U) concrete_fun.

HB.mixin Record PreCat_IsConcrete T of ConcreteQuiver T & PreCat T := {
  concrete1 : forall (a : T), concrete <$> \idmap_a = idfun;
  concrete_comp : forall (a b c : T) (f : a ~> b) (g : b ~> c),
    concrete <$> (f \; g) = ((concrete <$> g) \o (concrete <$> f))%FUN;
}.
Unset Universe Checking.
#[short(type="concrete_precat")]
HB.structure Definition ConcretePreCat : Set :=
  { C of PreCat C & ConcreteQuiver C & PreCat_IsConcrete C }.
#[short(type="concrete_cat")]
HB.structure Definition ConcreteCat : Set :=
  { C of Cat C & ConcreteQuiver C & PreCat_IsConcrete C }.
Set Universe Checking.

HB.instance Definition _ (C : concrete_precat) :=
  PreFunctor_IsFunctor.Build C U concrete (@concrete1 _) (@concrete_comp _).
HB.instance Definition _ (C : ConcreteCat.type) :=
  PreFunctor_IsFunctor.Build C U concrete (@concrete1 _) (@concrete_comp _).

HB.instance Definition _ := Quiver_IsPreConcrete.Build U (fun _ _ => id).
HB.instance Definition _ := PreConcrete_IsConcrete.Build U (fun _ _ _ _ => id).
HB.instance Definition _ := PreCat_IsConcrete.Build U
   (fun=> erefl) (fun _ _ _ _ _ => erefl).

Unset Universe Checking.
HB.instance Definition _ := Quiver_IsPreConcrete.Build quiver (fun _ _ => id).
HB.instance Definition _ := Quiver_IsPreConcrete.Build precat (fun _ _ => id).
HB.instance Definition _ := Quiver_IsPreConcrete.Build cat (fun _ _ => id).
Lemma quiver_concrete_subproof : PreConcrete_IsConcrete quiver.
Proof.
constructor=> C D F G FG; apply: prefunctorP.
  by move=> x; congr (_ x); apply: FG.
by move=> *; apply: Prop_irrelevance.
Qed.
HB.instance Definition _ := quiver_concrete_subproof.

Lemma precat_concrete_subproof : PreConcrete_IsConcrete precat.
Proof.
constructor=> C D F G FG; apply: functorP.
  by move=> x; congr (_ x); apply: FG.
by move=> *; apply: Prop_irrelevance.
Qed.
HB.instance Definition _ := precat_concrete_subproof.

Lemma cat_concrete_subproof : PreConcrete_IsConcrete cat.
Proof.
constructor=> C D F G FG; apply: functorP.
  by move=> x; congr (_ x); apply: FG.
by move=> *; apply: Prop_irrelevance.
Qed.
HB.instance Definition _ := cat_concrete_subproof.
HB.instance Definition _ := PreCat_IsConcrete.Build precat
   (fun=> erefl) (fun _ _ _ _ _ => erefl).
HB.instance Definition _ := PreCat_IsConcrete.Build cat
   (fun=> erefl) (fun _ _ _ _ _ => erefl).
Set Universe Checking.

(* constant functor *)
Definition cst (C D : quiver) (c : C) := fun of D => c.
Arguments cst {C} D c.
HB.instance Definition _ {C D : precat} (c : C) :=
  IsPreFunctor.Build D C (cst D c) (fun _ _ _ => idmap).
HB.instance Definition _ {C D : cat} (c : C) :=
  PreFunctor_IsFunctor.Build D C (cst D c) (fun=> erefl)
    (fun _ _ _ _ _ => esym (compo1 idmap)).

(* opposite category *)
Definition catop (C : U) : U := C.
Notation "C ^op" := (catop C)
   (at level 2, format "C ^op") : cat_scope.
HB.instance Definition _ (C : quiver) :=
  IsQuiver.Build C^op (fun a b => hom b a).
HB.instance Definition _ (C : precat) :=
  Quiver_IsPreCat.Build (C^op) (fun=> idmap) (fun _ _ _ f g => g \; f).
HB.instance Definition _ (C : cat) := PreCat_IsCat.Build (C^op)
   (fun _ _ _ => compo1 _) (fun _ _ _ => comp1o _)
   (fun _ _ _ _ _ _ _ => esym (compoA _ _ _)).

HB.instance Definition _ {C : precat} {c : C} :=
  IsPreFunctor.Build C _ (hom c) (fun a b f g => g \; f).
Lemma hom_Fhom_subproof (C : cat) (x : C) :
  PreFunctor_IsFunctor _ _ (hom x).
Proof. by split=> *; apply/funext => h; [apply: compo1 | apply: compoA]. Qed.
HB.instance Definition _ {C : cat} {c : C} := hom_Fhom_subproof c.

Check fun (C : cat) (x : C) => hom x : C ~>_cat U.

Lemma hom_op {C : quiver} (c : C^op) : hom c = (@hom C)^~ c.
Proof. reflexivity. Qed.

Lemma homFhomx {C : precat} (a b c : C) (f : a ~> b) (g : c ~> a) :
  (hom c <$> f) g = g \; f.
Proof. reflexivity. Qed.

(* nary product of categories *)
Definition dprod {I : U} (C : I -> U) := forall i, C i.

Section hom_dprod.
Context {I : U} (C : I -> quiver).
Definition dprod_hom_subdef (a b : dprod C) := forall i, a i ~> b i.
HB.instance Definition _ := IsQuiver.Build (dprod C) dprod_hom_subdef.
End hom_dprod.
Arguments dprod_hom_subdef /.

Section precat_dprod.
Context {I : U} (C : I -> precat).
Definition dprod_idmap_subdef (a : dprod C) : a ~> a := fun=> idmap.
Definition dprod_comp_subdef (a b c : dprod C) (f : a ~> b) (g : b ~> c) : a ~> c :=
  fun i => f i \; g i.
HB.instance Definition _ := IsPreCat.Build (dprod C)
   dprod_idmap_subdef dprod_comp_subdef.
End precat_dprod.
Arguments dprod_idmap_subdef /.
Arguments dprod_comp_subdef /.

Section cat_dprod.
Context {I : U} (C : I -> cat).
Local Notation type := (dprod C).
Lemma dprod_is_cat : PreCat_IsCat type.
Proof.
split=> [a b f|a b f|a b c d f g h]; apply/funext => i;
[exact: comp1o | exact: compo1 | exact: compoA].
Qed.
HB.instance Definition _ := dprod_is_cat.
End cat_dprod.

(* binary product *)
Section hom_prod.
Context {C D : quiver}.
Definition prod_hom_subdef (a b : C * D) := ((a.1 ~> b.1) * (a.2 ~> b.2))%type.
HB.instance Definition _ := IsQuiver.Build (C * D)%type prod_hom_subdef.
End hom_prod.

Section precat_prod.
Context {C D : precat}.
HB.instance Definition _ := IsPreCat.Build (C * D)%type (fun=> (idmap, idmap))
  (fun a b c (f : a ~> b) (g : b ~> c) => (f.1 \; g.1, f.2 \; g.2)).
End precat_prod.

Section cat_prod.
Context {C D : cat}.
Local Notation type := (C * D)%type.
Lemma prod_is_cat : PreCat_IsCat type.
Proof.
split=> [[a1 a2] [b1 b2] [f1 f2]|[a1 a2] [b1 b2] [f1 f2]|
  [a1 a2] [b1 b2] [c1 c2] [d1 d2] [f1 f2] [g1 g2] [h1 h2]]; congr (_, _) => //=;
by [exact: comp1o | exact: compo1 | exact: compoA].
Qed.
HB.instance Definition _ := prod_is_cat.
End cat_prod.

(* naturality *)
HB.mixin Record IsNatural (C D : precat) (F G : C ~>_quiver D)
     (n : forall c, F c ~> G c) := {
   natural : forall (a b : C) (f : a ~> b),
     F <$> f \; n b = n a \; G <$> f
}.
Unset Universe Checking.
HB.structure Definition Natural (C D : precat)
   (F G : C ~>_quiver D) : Set :=
  { n of @IsNatural C D F G n }.
Set Universe Checking.
HB.instance Definition _  (C D : precat) :=
  IsQuiver.Build (PreFunctor.type C D) (@Natural.type C D).
HB.instance Definition _  (C D : cat) :=
  IsQuiver.Build (Functor.type C D) (@Natural.type C D).
Arguments natural {C D F G} n [a b] f : rename.

Check fun (C D : cat) (F G : C ~> D) => F ~>_(C ~>_cat D) G.

Lemma naturalx (C : precat) (D : concrete_precat)
  (F G : C ~>_quiver D) (n : F ~> G)  (a b : C) (f : a ~> b) g :
    (concrete <$> n b) ((concrete <$> F <$> f) g) =
    (concrete <$> G <$> f) ((concrete <$> n a) g).
Proof.
have /(congr1 (fun h  => (concrete <$> h) g)) := natural n f.
by rewrite !Fcomp.
Qed.
Arguments naturalx {C D F G} n [a b] f.

Lemma naturalU (C : precat) (F G : C ~>_quiver U) (n : F ~> G)
   (a b : C) (f : a ~> b) g :  n b (F^$ f g) = G^$ f (n a g).
Proof. exact: (naturalx n). Qed.

Lemma natP (C D : precat) (F G : C ~>_quiver D) (n m : F ~> G) :
  Natural.sort n = Natural.sort m -> n = m.
Proof.
case: n m => [/= n nP] [/= m mP] enm.
elim: _ / enm in mP *; congr Natural.Pack.
case: nP mP => [[?]] [[?]]; congr Natural.Class.
congr IsNatural.Axioms_.
exact: Prop_irrelevance.
Qed.

Notation "F ~~> G" := (F ~>_(homs quiver) G)
  (at level 99, G at level 200, format "F  ~~>  G").
Notation "F ~~> G :> C ~> D" := (F ~> G :> (C ~>_quiver D))
  (at level 99, G at level 200, C, D at level 0,
   format "F  ~~>  G  :>  C  ~>  D").

Definition natural_id {C D : precat} (F : C ~>_quiver D) (a : C) := \idmap_(F a).
Definition natural_id_natural (C D : cat) (F : C ~>_quiver D) :
  IsNatural C D F F (natural_id F).
Proof. by constructor=> a b f; rewrite /natural_id/= compo1 comp1o. Qed.
HB.instance Definition _ C D F := @natural_id_natural C D F.

Check fun {C D : cat} (F : C ~>_quiver D) => natural_id F : F ~> F.

Definition natural_comp {C D : precat} (F G H : C ~>_quiver D)
   (m : F ~> G) (n : G ~> H) (a : C) := m a \; n a.
Definition natural_comp_natural (C D : cat) (F G H : C ~>_quiver D) m n :
  IsNatural C D F H (@natural_comp C D F G H m n).
Proof.
constructor=> a b f; rewrite /natural_comp/=.
by rewrite compoA natural -compoA natural compoA.
Qed.
HB.instance Definition _ C D F G H m n := @natural_comp_natural C D F G H m n.

HB.instance Definition _ {C D : cat} :=
  Quiver_IsPreCat.Build (PreFunctor.type C D) natural_id natural_comp.
HB.instance Definition _ {C D : cat} :=
  Quiver_IsPreCat.Build (Functor.type C D) natural_id natural_comp.

Lemma prefunctor_cat {C D : cat} : PreCat_IsCat (PreFunctor.type C D).
Proof.
constructor => [F G f|F G f|F G H J f g h].
- by apply/natP/funext => a; rewrite /= /natural_comp comp1o.
- by apply/natP/funext => a; rewrite /= /natural_comp compo1.
- by apply/natP/funext => a; rewrite /= /natural_comp compoA.
Qed.
HB.instance Definition _ C D := @prefunctor_cat C D.

Lemma functor_cat {C D : cat} : PreCat_IsCat (Functor.type C D).
Proof.
constructor => [F G f|F G f|F G H J f g h].
- by apply/natP/funext => a; rewrite /= /natural_comp comp1o.
- by apply/natP/funext => a; rewrite /= /natural_comp compo1.
- by apply/natP/funext => a; rewrite /= /natural_comp compoA.
Qed.
HB.instance Definition _ C D := @functor_cat C D.

Section nat_map_left.
Context {C D E : precat} {F G : C ~> D}.

Definition nat_lmap (H : D ~>_quiver E) (n : forall c, F c ~> G c) :
  forall c, (H \o F)%FUN c ~> (H \o G)%FUN c := fun c => H <$> n c.

Fail Check fun (H : D ~> E) (n : F ~~> G) => nat_lmap H n : H \o F ~~> H \o G.

Lemma nat_lmap_is_natural (H : D ~> E) (n : F ~~> G) :
  IsNatural C E (H \o F) (H \o G) (nat_lmap H n).
Proof. by constructor=> a b f; rewrite /nat_lmap/= -!Fcomp natural. Qed.
HB.instance Definition _ H n := nat_lmap_is_natural H n.

Check fun (H : D ~> E) (n : F ~~> G) => nat_lmap H n : H \o F ~~> H \o G.

End nat_map_left.

Notation "F <o$> n" := (nat_lmap F n)
   (at level 58, format "F  <o$>  n", right associativity) : cat_scope.

Section nat_map_right.
Context {C D E : precat} {F G : C ~> D}.

Definition nat_rmap (H : E -> C) (n : forall c, F c ~> G c) :
  forall c, (F \o H)%FUN c ~> (G \o H)%FUN c := fun c => n (H c).
Lemma nat_rmap_is_natural (H : E ~> C :> quiver) (n : F ~~> G) :
  IsNatural E D (F \o H)%FUN (G \o H)%FUN (nat_rmap H n).
Proof. by constructor=> a b f; rewrite /nat_lmap/= natural. Qed.
HB.instance Definition _ H n := nat_rmap_is_natural H n.

End nat_map_right.

Notation "F <$o> n" := (nat_rmap F n)
   (at level 58, format "F  <$o>  n", right associativity) : cat_scope.

Definition delta (C D : cat) : C -> (D ~> C) := cst D.
Arguments delta C D : clear implicits.

Definition map_delta {C D : cat} (a b : C) (f : a ~> b) :
  delta C D a ~> delta C D b.
Proof.
apply: (@Natural.Pack _ _ (cst D a) (cst D b) (fun x => f)).
apply: Natural.Class; apply: (IsNatural.Build _ _ _ _ _).
by move=> a' b' ?; rewrite compo1 comp1o.
Defined.

HB.instance Definition _ {C D : cat} :=
  IsPreFunctor.Build C (D ~> C) (delta C D) (@map_delta C D).

Lemma delta_functor {C D : cat} : PreFunctor_IsFunctor _ _ (delta C D).
Proof. by constructor=> [a|a b c f g]; exact/natP. Qed.
HB.instance Definition _ C D := @delta_functor C D.

HB.mixin Record IsMonad (C : precat) (M : C -> C) of @PreFunctor C C M := {
  unit : idfun ~~> M;
  join : (M \o M)%FUN ~~> M;
  bind : forall (a b : C), (a ~> M b) -> (M a ~> M b);
  bindE : forall a b (f : a ~> M b), bind a b f = M <$> f \; join b;
  unit_join : forall a, (M <$> unit a) \; join _ = idmap;
  join_unit : forall a, join _ \; (M <$> unit a) = idmap;
  join_square : forall a, M <$> join a \; join _ = join _ \; join _
}.

#[short(type="premonad")]
HB.structure Definition PreMonad (C : precat) :=
   {M of @PreFunctor C C M & IsMonad C M}.
#[short(type="monad")]
HB.structure Definition Monad (C : precat) :=
   {M of @Functor C C M & IsMonad C M}.

HB.factory Record IsJoinMonad (C : precat) (M : C -> C) of @PreFunctor C C M := {
  unit : idfun ~~> M;
  join : (M \o M)%FUN ~~> M;
  unit_join : forall a, (M <$> unit a) \; join _ = idmap;
  join_unit : forall a, join _ \; (M <$> unit a) = idmap;
  join_square : forall a, M <$> join a \; join _ = join _ \; join _
}.
HB.builders Context C M of IsJoinMonad C M.
  HB.instance Definition _ := IsMonad.Build C M
    (fun a b f => erefl) unit_join join_unit join_square.
HB.end.

HB.mixin Record IsCoMonad (C : precat) (M : C -> C) of @IsPreFunctor C C M := {
  counit : M ~~> idfun;
  cojoin : M ~~> (M \o M)%FUN;
  cobind : forall (a b : C), (M a ~> b) -> (M a ~> M b);
  cobindE : forall a b (f : M a ~> b), cobind a b f = cojoin _ \; M <$> f;
  unit_cojoin : forall a, (M <$> counit a) \; cojoin _ = idmap;
  join_counit : forall a, cojoin _ \; (M <$> counit a) = idmap;
  cojoin_square : forall a, cojoin _ \; M <$> cojoin a = cojoin _ \; cojoin _
}.
#[short(type="precomonad")]
HB.structure Definition PreCoMonad (C : precat) :=
   {M of @PreFunctor C C M & IsCoMonad C M}.
#[short(type="comonad")]
HB.structure Definition CoMonad (C : precat) :=
   {M of @Functor C C M & IsCoMonad C M}.

HB.factory Record IsJoinCoMonad (C : precat) (M : C -> C) of @IsPreFunctor C C M := {
  counit : M ~~> idfun;
  cojoin : M ~~> (M \o M)%FUN;
  unit_cojoin : forall a, (M <$> counit a) \; cojoin _ = idmap;
  join_counit : forall a, cojoin _ \; (M <$> counit a) = idmap;
  cojoin_square : forall a, cojoin _ \; M <$> cojoin a = cojoin _ \; cojoin _
}.
HB.builders Context C M of IsJoinCoMonad C M.
  HB.instance Definition _ := IsCoMonad.Build C M
    (fun a b f => erefl) unit_cojoin join_counit cojoin_square.
HB.end.

Lemma idFmap (C : cat) (a b : C) (f : a ~> b) : idfun <$> f = f.
Proof. by []. Qed.

Lemma compFmap (C D E : cat) (F : C ~> D) (G : D ~> E) (a b : C) (f : a ~> b) :
  (G \o F) <$> f = G <$> F <$> f.
Proof. by []. Qed.

(* yoneda *)
Section hom_repr.
Context {C : cat} (F : C ~>_cat U).

Definition homF : C -> U := fun c => hom c ~~> F.

Section nat.
Context (x y : C) (xy : x ~> y).

(* Goal hom x ~~> F -> hom y ~~> F *)
Context (n : hom x ~~> F).
Definition homFhom c : hom y c ~> F c := fun g => n _ (xy \; g).

Lemma homFhom_natural_subdef : IsNatural C U (hom y) F homFhom.
Proof.
by split=> a b f /=; apply/funext => g /=;
   rewrite /homFhom !Ucompx/= !naturalU/= Fcomp.
Qed.
HB.instance Definition _ := homFhom_natural_subdef.
End nat.
Arguments homFhom / : clear implicits.

HB.about IsPreFunctor.Build.
Check homFhom : forall x y : C, (x ~> y) -> (homF x -> homF y).
HB.instance Definition _ := IsPreFunctor.Build _ _ homF homFhom.
Lemma homF_functor_subproof : PreFunctor_IsFunctor _ _ homF.
Proof.
split=> [a|a b c f g].
  apply/funext => -[/= f natf].
  apply: natP => //=; apply: funext => b; apply: funext => g/=.
  by rewrite comp1o.
apply/funext => -[/= h natf].
apply: natP => //=; apply: funext => d; apply: funext => k/=.
by rewrite compoA.
Qed.
HB.instance Definition _ := homF_functor_subproof.

Section pointed.
Context (c : C).
Definition hom_repr : homF c ~> F c := fun f => f _ idmap.
Arguments hom_repr /.

Definition repr_hom (fc : F c) a : hom c a ~> F a :=
  fun f => F^$ f fc.
Arguments repr_hom / : clear implicits.
Lemma repr_hom_subdef (fc : F c) : IsNatural _ _ _ _ (repr_hom fc).
Proof. by split=> a b f /=; apply/funext=> x; rewrite !Ucompx/= Fcomp. Qed.
HB.instance Definition _ {fc : F c} := repr_hom_subdef fc.

Definition repr_hom_nat : F c ~> homF c := repr_hom.

Lemma hom_reprK : cancel hom_repr repr_hom_nat.
Proof.
move=> f; apply/natP; apply/funext => a; apply/funext => g /=.
by rewrite -naturalU/=; congr (f _ _); apply: comp1o.
Qed.
Lemma repr_homK : cancel (repr_hom : F c ~> homF c) hom_repr.
Proof. by move=> fc; rewrite /= F1. Qed.
End pointed.
Arguments hom_repr /.
Arguments repr_hom /.

Lemma hom_repr_natural_subproof : IsNatural _ _ _ _ hom_repr.
Proof.
split=> a b f /=; apply/funext => n /=; rewrite !Ucompx/= compo1/=.
by rewrite -naturalU/=; congr (n _ _); apply/esym/comp1o.
Qed.
HB.instance Definition _ := hom_repr_natural_subproof.

(* show this from the previous proof *)
Lemma hom_natural_repr_subproof : IsNatural _ _ _ _ repr_hom_nat.
Proof.
split=> a b f /=; apply: funext => fa /=; rewrite !Ucompx/=.
apply: natP; apply: funext => c /=; apply: funext => d /=.
by rewrite Fcomp Ucompx/=.
Qed.
HB.instance Definition _ := hom_natural_repr_subproof.

Definition hom_repr_nat : homF ~~> F := hom_repr.
Definition repr_hom_nat_nat : F ~~> homF := repr_hom_nat.

End hom_repr.

(* comma categories *)
Module comma.
Section homcomma.
Context {C D E : precat} (F : C ~> E) (G : D ~> E).

Definition type := { x : C * D & F x.1 ~> G x.2 }.
Definition hom_subdef (a b : type) := {
    f : tag a ~> tag b & F <$> f.1 \; tagged b = tagged a \; G <$> f.2
  }.
HB.instance Definition _ := IsQuiver.Build type hom_subdef.
End homcomma.
Arguments hom_subdef /.
Section comma.
Context {C D E : cat} (F : C ~> E) (G : D ~> E).
Notation type := (type F G).

Program Definition idmap_subdef (a : type) : a ~> a := @Tagged _ idmap _ _.
Next Obligation. by rewrite !F1 comp1o compo1. Qed.
Program Definition comp_subdef (a b c : type)
  (f : a ~> b) (g : b ~> c) : a ~> c :=
  @Tagged _ (tag f \; tag g) _ _.
Next Obligation. by rewrite !Fcomp -compoA (tagged g) compoA (tagged f) compoA. Qed.
HB.instance Definition _ := IsPreCat.Build type idmap_subdef comp_subdef.
Arguments idmap_subdef /.
Arguments comp_subdef /.

Lemma comma_homeqP (a b : type) (f g : a ~> b) : projT1 f = projT1 g -> f = g.
Proof.
case: f g => [f fP] [g +]/= eqfg; case: _ / eqfg => gP.
by congr existT; apply: Prop_irrelevance.
Qed.

Lemma comma_is_cat : PreCat_IsCat type.
Proof.
by split=> [[a fa] [b fb] [*]|[a fa] [b fb] [*]|*];
   apply/comma_homeqP; rewrite /= ?(comp1o, compo1, compoA).
Qed.
HB.instance Definition _ := comma_is_cat.
End comma.
End comma.
Notation "F `/` G" := (@comma.type _ _ _ F G)
  (at level 40, G at level 40, format "F `/` G") : cat_scope.
Notation "a /` G" := (cst unit a `/` G)
  (at level 40, G at level 40, format "a /` G") : cat_scope.
Notation "F `/ b" := (F `/` cst unit b)
  (at level 40, b at level 40, format "F `/ b") : cat_scope.
Notation "a / b" := (cst unit a `/ b) : cat_scope.

Definition obj (C : quiver) : Type := C.
HB.mixin Record IsInitial {C : quiver} (i : obj C) := {
  to : forall c, i ~> c;
  to_unique : forall c (f : i ~> c), f = to c
}.
#[short(type="initial")]
HB.structure Definition Initial {C : quiver} := {i of IsInitial C i}.

HB.mixin Record IsTerminal {C : quiver} (t : obj C) := {
  from : forall c, c ~> t;
  from_unique : forall c (f : c ~> t), f = from c
}.
#[short(type="terminal")]
HB.structure Definition Terminal {C : quiver} := {t of IsTerminal C t}.
#[short(type="universal")]
HB.structure Definition Universal {C : quiver} :=
  {u of Initial C u & Terminal C u}.

(* Definition hom' {C : precat} (a b : C) := a ~> b. *)
(* (* Bug *) *)
(* Identity Coercion hom'_hom : hom' >-> hom. *)

(* HB.mixin Record IsMono {C : precat} (b c : C) (f : hom b c) := { *)
(*   monoP : forall (a : C) (g1 g2 : a ~> b), g1 \; f = g2 \; f -> g1 = g2 *)
(* }. *)
(* #[short(type="mono")] *)
(* HB.structure Definition Mono {C : precat} (a b : C) := {m of IsMono C a b m}. *)
(* Notation "a >~> b" := (mono a b) *)
(*    (at level 99, b at level 200, format "a  >~>  b") : cat_scope. *)
(* Notation "C >~>_ T D" := (@mono T C D) *)
(*   (at level 99, T at level 0, only parsing) : cat_scope. *)

(* HB.mixin Record IsEpi {C : precat} (a b : C) (f : hom a b) := { *)
(*   epiP :  forall (c : C) (g1 g2 : b ~> c), g1 \o f = g2 \o f -> g1 = g2 *)
(* }. *)
(* #[short(type="epi")] *)
(* HB.structure Definition Epi {C : precat} (a b : C) := {e of IsEpi C a b e}. *)
(* Notation "a ~>> b" := (epi a b) *)
(*    (at level 99, b at level 200, format "a  ~>>  b") : cat_scope. *)
(* Notation "C ~>>_ T D" := (@epi T C D) *)
(*   (at level 99, T at level 0, only parsing) : cat_scope. *)

(* #[short(type="iso")] *)
(* HB.structure Definition Iso {C : precat} (a b : C) := *)
(*    {i of @Mono C a b i & @Epi C a b i}. *)
(* Notation "a <~> b" := (epi a b) *)
(*    (at level 99, b at level 200, format "a  <~>  b") : cat_scope. *)
(* Notation "C <~>_ T D" := (@epi T C D) *)
(*   (at level 99, T at level 0, only parsing) : cat_scope. *)

HB.mixin Record IsRightAdjoint (D C : precat) (R : D -> C)
    of @PreFunctor D C R := {
  L_ : C ~> D;
  phi : forall c d, (L_ c ~> d) -> (c ~> R d);
  psy : forall c d, (c ~> R d) -> (L_ c ~> d);
  phi_psy c d : (phi c d \o psy c d)%FUN = @id (c ~> R d);
  psy_phi c d : (psy c d \o phi c d)%FUN = @id (L_ c ~> d)
}.
#[short(type="right_adjoint")]
HB.structure Definition RightAdjoint (D C : precat) :=
  { R of @Functor D C R & IsRightAdjoint D C R }.
Arguments L_ {_ _}.
Arguments phi {D C s} {c d}.
Arguments psy {D C s} {c d}.


HB.mixin Record PreCat_IsMonoidal C of PreCat C := {
  onec : C;
  (* prod1 : @hom precat (C * C)%type C ; *) 
  prod : (C * C)%type ~>_precat C;
}.
#[short(type="premonoidal")]
#[verbose]
HB.structure Definition PreMonoidal := { C of PreCat C & PreCat_IsMonoidal C }.
Notation premonoidal := premonoidal.
Arguments prod {C} : rename.
Notation "a * b" := (prod (a, b)) : cat_scope.
Reserved Notation "f <*> g"   (at level 40, g at level 40, format "f  <*>  g").
Notation "f <*> g" := (prod^$ (f, g)) (only printing) : cat_scope.
Notation "f <*> g" := (prod^$ ((f, g) : (_, _) ~> (_, _)))
  (only parsing) : cat_scope.
Notation "1" := onec : cat_scope.

Definition hom_cast {C : quiver} {a a' : C} (eqa : a = a') {b b' : C} (eqb : b = b') :
  (a ~> b) -> (a' ~> b').
Proof. now elim: _ / eqa; elim: _ / eqb. Defined.

HB.mixin Record PreFunctor_IsMonoidal (C D : premonoidal) F of
    @PreFunctor C D F := {
  fun_one : F 1 = 1;
  fun_prod : forall (x y : C), F (x * y) = F x * F y;
}.
#[short(type="monoidal_prefunctor")]
HB.structure Definition MonoidalPreFunctor C D :=
  { F of @PreFunctor_IsMonoidal C D F }.
Arguments fun_prod {C D F x y} : rename.
(* Arguments fun_prodF {C D F x x'} f {y y'} g : rename. *)
Unset Universe Checking.
HB.instance Definition _ := IsQuiver.Build premonoidal MonoidalPreFunctor.type.
Set Universe Checking.

HB.instance Definition _ (C : quiver) :=
  IsPreFunctor.Build (C * C)%type C fst
     (fun (a b : C * C) (f : a ~> b) => f.1).
HB.instance Definition _ (C : quiver) :=
  IsPreFunctor.Build (C * C)%type C snd
     (fun (a b : C * C) (f : a ~> b) => f.2).

Definition prod3l {C : premonoidal} (x : C * C * C) : C :=
  (x.1.1 * x.1.2) * x.2.
HB.instance Definition _ {C : premonoidal} :=
  IsPreFunctor.Build _ C prod3l
   (fun a b (f : a ~> b) => (f.1.1 <*> f.1.2) <*> f.2).

Definition prod3r {C : premonoidal} (x : C * C * C) : C :=
  x.1.1 * (x.1.2 * x.2).
HB.instance Definition _ {C : premonoidal} :=
  IsPreFunctor.Build _ C prod3r
   (fun a b (f : a ~> b) => f.1.1 <*> (f.1.2 <*> f.2)).

Definition prod1r {C : premonoidal} (x : C) : C := 1 * x.
HB.instance Definition _ {C : premonoidal} :=
  IsPreFunctor.Build C C prod1r
   (fun (a b : C) (f : a ~> b) => \idmap_1 <*> f).

Definition prod1l {C : premonoidal} (x : C) : C := x * 1.
HB.instance Definition _ {C : premonoidal} :=
  IsPreFunctor.Build C C prod1l
   (fun (a b : C) (f : a ~> b) => f <*> \idmap_1).

HB.mixin Record PreMonoidal_IsMonoidal C of PreMonoidal C := {
  prodA  : prod3l ~~> prod3r;
  prod1c : prod1r ~~> idfun;
  prodc1 : prod1l ~~> idfun;
  prodc1c : forall (x y : C),
      prodA (x, 1, y) \; \idmap_x <*> prod1c y = prodc1 x <*> \idmap_y;
  prodA4 : forall (w x y z : C),
      prodA (w * x, y, z) \; prodA (w, x, y * z) =
        prodA (w, x, y) <*> \idmap_z \; prodA (w, x * y, z) \; \idmap_w <*> prodA (x, y, z);
}.

Unset Universe Checking.
#[short(type="monoidal")]
#[verbose]
HB.structure Definition Monoidal : Set :=
  { C of PreMonoidal_IsMonoidal C & PreMonoidal C }.
Set Universe Checking.

(******************************************************************)


Record cospan (Q : quiver) (A B : Q) := Cospan {
  top : Q;
  left2top : A ~> top;
  right2top : B ~> top
}.

Section cospans.
Variables (Q : precat) (A B : Q).
Record cospan_map (c c' : cospan A B) := CospanMap {
  top_map : top c ~> top c';
  left2top_map : left2top c \; top_map = left2top c';
  right2top_map : right2top c \; top_map = right2top c';
}.
HB.instance Definition _ := IsQuiver.Build (cospan A B) cospan_map.

Lemma cospan_mapP (c c' : cospan A B) (f g : c ~> c') :
  top_map f = top_map g <-> f = g.
Admitted.
End cospans.

Section cospans_in_cat.
Variables (Q : cat) (A B : Q).
Definition cospan_idmap (c : cospan A B) :=
  @CospanMap Q A B c c idmap (compo1 _) (compo1 _).
Program Definition cospan_comp (c1 c2 c3 : cospan A B)
    (f12 : c1 ~> c2) (f23 : c2 ~> c3) :=
  @CospanMap Q A B c1 c3 (top_map f12 \; top_map f23) _ _.
Next Obligation. by rewrite compoA !left2top_map. Qed.
Next Obligation. by rewrite compoA !right2top_map. Qed.
HB.instance Definition _ := IsPreCat.Build (cospan A B) cospan_idmap cospan_comp.

Lemma cospan_are_cats : PreCat_IsCat (cospan A B).
Proof.
constructor=> [a b f|a b f|a b c d f g h].
- by apply/cospan_mapP => /=; rewrite comp1o.
- by apply/cospan_mapP => /=; rewrite compo1.
- by apply/cospan_mapP => /=; rewrite compoA.
Qed.
HB.instance Definition _ := cospan_are_cats.
End cospans_in_cat.

Section spans_and_co.
Variables (Q : quiver) (A B : Q).
Definition span := @cospan Q^op A B.
Definition bot  (s : span) : Q := top s.
Definition bot2left  (s : span) : bot s ~>_Q A := left2top s.
Definition bot2right (s : span) : bot s ~>_Q B := right2top s.
Definition Span (C : Q) (f : C ~> A) (g : C ~> B) : span :=
   @Cospan Q^op A B C f g.
End spans_and_co.

HB.instance Definition _ (Q : precat) (A B : Q) :=
  Quiver.copy (span A B) (@cospan Q^op A B)^op.
HB.instance Definition _ (Q : cat) (A B : Q) :=
  Cat.copy (span A B) (@cospan Q^op A B)^op.

Section bot_map.
Variables (C : cat) (A B : C) (s s' : span A B) (f : s ~> s').
Definition bot_map : bot s ~> bot s' := top_map f.
Lemma bot2left_map : bot_map \; bot2left s' = bot2left s.
Proof. exact: left2top_map f. Qed.
Lemma bot2right_map : bot_map \; bot2right s' = bot2right s.
Proof. exact: right2top_map f. Qed.
End bot_map.

HB.mixin Record isPrePullback (Q : precat) (A B : Q)
     (c : cospan A B) (s : span A B) := {
   is_square : bot2left s \; left2top c = bot2right s \; right2top c;
}.
#[short(type=prepullback)]
HB.structure Definition PrePullback Q A B (c : cospan A B) :=
  {s of isPrePullback Q A B c s}.
Arguments prepullback {Q A B} c.

Section prepullback.
Variables (Q : precat) (A B : Q) (c : cospan A B).
HB.instance Definition _ :=
  IsQuiver.Build (prepullback c)
    (fun a b => (a : span A B) ~>_(span A B) (b : span A B)).
Lemma eq_prepullbackP (p q : prepullback c) :
  p = q :> span _ _ <-> p = q.
Admitted.
End prepullback.
Section prepullback.
Variables (Q : cat) (A B : Q) (csp : cospan A B).
(* TODO: why can't we do that? *)
(* HB.instance Definition _ := Cat.on (prepullback csp). *)
HB.instance Definition _ :=
  Quiver_IsPreCat.Build (prepullback csp)
    (fun a => \idmap_(a : span A B))
      (* TODO: study how to make this coercion trigger
               even when the target is not reduced to span *)
    (fun a b c f g => f \; g).
Lemma prepullback_is_cat : PreCat_IsCat (prepullback csp).
Proof. (* should be copied from the cat on span *)
constructor=> [a b f|a b f|a b c d f g h];
 [exact: comp1o|exact: compo1|exact: compoA].
Qed.
End prepullback.

HB.tag Definition pb_terminal (Q : precat)
  (A B : Q) (c : cospan A B) (s : prepullback c) :
    obj (prepullback c) := s.

#[wrapper]
HB.mixin Record prepullback_isTerminal (Q : precat)
    (A B : Q) (c : cospan A B) 
    (s : span A B) of isPrePullback Q A B c s := {
  prepullback_terminal :
    IsTerminal (prepullback c) (pb_terminal s)
}.
#[short(type="pullback"), verbose]
HB.structure Definition Pullback (Q : precat)
    (A B : Q) (c : cospan A B) :=
  {s of isPrePullback Q A B c s 
      & IsTerminal (prepullback c) (pb_terminal s) }.

Notation pbsquare u v f g :=
  (Pullback _ (Cospan f g) (Span u v)).

Notation "P <=> Q" := ((P -> Q) * (Q -> P))%type (at level 70).

(********************************************************************)
(********************************************************************)

(*** ENRICHED CATEGORIES *)

Declare Scope encat_scope.
Delimit Scope encat_scope with encat.
Local Open Scope encat_scope.

(* Enrichment in a monoidal category, following 
   https://ncatlab.org/nlab/show/enriched+category
*)
HB.mixin Record IsEnQuiver (V: Type) C := {
    hom_object : C -> C -> V 
  }.
Unset Universe Checking.
HB.structure Definition EnQuiver (V: Type) : Set :=
  { C of IsEnQuiver V C }.
Set Universe Checking.

(* Monoidal precategory with the enrichment operators (no axioms) *)
HB.mixin Record IsEnPreCat (V: PreMonoidal.type) C of
  EnQuiver (PreMonoidal.sort V) C := {  
    id_element : forall (a: C),
      @hom V onec (hom_object a a) ;
    comp_morphism : forall (a b c: C),
      @hom V (@hom_object V C b c * @hom_object V C a b)
             (@hom_object V C a c) 
}.    
Unset Universe Checking. 
HB.structure Definition EnPreCat (V: PreMonoidal.type) : Set :=
  { C of IsEnPreCat V C }.
Set Universe Checking.

Notation "a ~^ b" := (hom_object a b)
   (at level 99, b at level 200, format "a ~^ b") : encat_scope.
Notation "a ~^_ ( V , C ) b" := (@hom_object V C a b)
  (at level 99, V at level 0, C at level 0, only parsing) : cat_scope.
Notation "~^IE a" := (id_element a)
   (at level 99, format "~^IE a") : cat_scope.
Notation "~^IE_ ( V , C ) a" := (@id_element V C a)
  (at level 99, V at level 0, C at level 0, only parsing) : cat_scope.
(* not working *)
Notation "~^CM a b c" := (comp_morphism a b c)
                          (at level 99,
                            format "~^CM a b c") : cat_scope.
Notation "~^CM_ ( V , C ) a b c" := (@comp_morphism V C a b c)
  (at level 99, V at level 0, C at level 0, only parsing) : cat_scope.

(* V-enriched category: 
   V is the monoidal category;
   C is the base category that gets enriched
*)
HB.mixin Record IsEnCat (V: Monoidal.type) C of EnPreCat V C := {    
   ecat_comp_assoc : forall a b c d: C,
    forall alpha:
      (((c ~^_(V,C) d) * (b ~^_(V,C) c)) * (a ~^_(V,C) b)) ~>_V
      ((c ~^_(V,C) d) * ((b ~^_(V,C) c) * (a ~^_(V,C) b))),
        ((@comp_morphism V C b c d) <*> (@idmap V (a ~^_(V,C) b))) \;
        (@comp_morphism V C a b d)
        =
        alpha \;
        ((@idmap V (c ~^_(V,C) d)) <*> (@comp_morphism V C a b c)) \;
        (@comp_morphism V C a c d) ; 

   ecat_comp_left_unital : forall a b: C,
    forall l: onec * (a ~^_(V,C) b) ~>_V (a ~^_(V,C) b), 
      l = ((@id_element V C b) <*> (@idmap V (a ~^_(V,C) b))) \;
          (@comp_morphism V C a b b) ;                                           
   ecat_comp_right_unital : forall a b: C,
    forall r: (a ~^_(V,C) b) * onec ~>_V (a ~^_(V,C) b), 
      r = ((@idmap V (a ~^_(V,C) b)) <*> (@id_element V C a)) \;
          (@comp_morphism V C a a b)                                         
}.
Unset Universe Checking.
#[verbose]
HB.structure Definition EnCat (V: Monoidal.type) : Set :=
                          { C of IsEnCat V C }.
Set Universe Checking.

(********************************************************************)

(*** DOUBLE CATEGORIES (without internal categories) *)

(* Strict double categories, from
   https://ncatlab.org/nlab/show/double+category
   (we don't use internal categories though)

   base obejcts (D0): C ; 

   vertical morphisms (for V-D0): @hom C ; 

   horizontal morphisms (for H-D0) : @hom (transpose C) ;

   horizontal morhisms as 2-objects (for D1): @HHomSet C ; 

   2-morphisms (for D1): @hom (@HHomSet C) 

   The definition of Strict Double Category (D0, D1) is given by:

   - vertical base category (V-D0)

   - horizontal base category (H-D0)

   - vertical 2-level category (D1)

   - source functor : D1 -> V-D0

   - target functor : D1 -> V-D0

   - horizontal unit functor : V-D0 -> D1

   - horizontal composition functor : D1 *0 D1 -> D1 
*)


(** Quivers for double categories *)

(* transpose for horizontal morphism quiver.
   HB.tag needed to identify transpose as lifter *)
HB.tag Definition transpose (C : quiver) : U := C. 
#[wrapper] HB.mixin Record IsHQuiver C of IsQuiver C := {
    is_hquiver : IsQuiver (transpose C)
}.
(* vertical and horizontal quivers, defining cells *)
Unset Universe Checking.
#[short(type="cquiver")] 
HB.structure Definition CQuiver : Set := { C of IsQuiver C & IsHQuiver C }.
Set Universe Checking.

HB.tag Definition hhom (c : CQuiver.type) : c -> c -> U := @hom (transpose c).

(* record to represent the set of morphims 
   (needed for 2-objects, i.e. horizontal morphisms) *)
Record Total2 T (h: T -> T -> U) : Type := HO {
    source : T;
    target : T;
    this_morph : h source target }.

(* the set of horizontal morphisms. *)
HB.tag Definition HHomSet (C: cquiver) := Total2 (@hhom C).

(* D1 quiver requirement (includes D0 quiver and its transpose). *)
#[wrapper] 
HB.mixin Record IsDQuiver T of CQuiver T := { is_dquiver : Quiver (HHomSet T) }.
Unset Universe Checking.
#[short(type="dquiver")]
HB.structure Definition DQuiver : Set := { C of IsDQuiver C }.
Set Universe Checking.


(** Horizonal D0-level category (H-D0) *)

(* Precategory based on the HQuiver (i.e. horizontal precategory on D0
   objects) *)
Unset Universe Checking.
#[wrapper]
HB.mixin Record IsHPreCat T of CQuiver T := {
    is_hprecat : Quiver_IsPreCat (transpose T) }.
#[short(type="hprecat")]
HB.structure Definition HPreCat : Set := { C of IsHPreCat C }.
Set Universe Checking.

(* The category based on the HQuiver (i.e. horizontal category on D0
   objects) *)
Unset Universe Checking.
#[wrapper] 
HB.mixin Record IsHCat T of HPreCat T := {
    is_hcat : PreCat_IsCat (transpose T) }.
#[short(type="hcat")]
HB.structure Definition HCat : Set := { C of IsHCat C }.
Set Universe Checking.


(** Horizontal 2-cell level category (D1 category) *)

(* Precategory based on the DQuiver (i.e. precategory D1). Gives: 
   vertical 2-cell identity morphism.  
   vertical 2-cell composition. *)
Unset Universe Checking.
#[wrapper]
HB.mixin Record IsC2PreCat T of DQuiver T := {
    is_c2precat : Quiver_IsPreCat (@HHomSet T) }.
#[short(type="c2precat")]
HB.structure Definition C2PreCat : Set := { C of IsC2PreCat C }.
Set Universe Checking.

(* The category based on the DQuiver (i.e. category D1). *)
Unset Universe Checking.
#[wrapper] 
HB.mixin Record IsC2Cat T of C2PreCat T := {
    is_c2cat : PreCat_IsCat (@HHomSet T) }.
#[short(type="c2cat")]
HB.structure Definition C2Cat : Set := { C of IsC2Cat C }.
Set Universe Checking.


(** Naked double category *)

(* Naked double category. Vertical (V-D0) and D1 categories. Double
   category without horizontal operators and functors *)
Unset Universe Checking.
#[short(type="vdcat")]
  HB.structure Definition VDCat : Set :=
  { C of Cat C & C2Cat C }.
Set Universe Checking.

(* Naked strict double category. Vertical (V-D0), horizontal (H-D0)
   and D1 categories. Strict double category without functors *)
Unset Universe Checking.
#[short(type="nd2cat")]
HB.structure Definition NDCat : Set := { C of Cat C & HCat C & C2Cat C }.
Set Universe Checking.


(** Auxiliary notions for Source, Target and 
    Horizontal Unit functors *)

(* homsets of 2-cell (D1) morphisms *)
Definition c2hom (D: DQuiver.type) : HHomSet D -> HHomSet D -> U :=
  @hom (HHomSet D).
(* type-level smart constructor for D1 homsets *)
Definition C2Hom (D: DQuiver.type) (a b c d: D) (h0: hhom a b)
  (h1: hhom c d) : U := c2hom (HO h0) (HO h1).

(* smart projections for: 
   source functor (for horizontal morphisms): D1 -> D0.
   defined as object-level function, by functoriality lifted to a
   (2-cell, vertical) morphism-level one *)
HB.tag Definition HSource C := fun (X: HHomSet C) => @source C (@hhom C) X.
(* target functor (for horizontal morphisms): D1 -> D0. *)
HB.tag Definition HTarget C := fun (X: HHomSet C) => @target C (@hhom C) X.

(* horizontal unit functor: D0 -> D1 *)
Definition hhunit (T: hprecat) (a: T) : HHomSet T :=
  @HO T (@hhom T) a a (@idmap (transpose T) a).
HB.tag Definition HUnit (C: hprecat) :=
  fun (x: HPreCat.sort C) => @hhunit C x. 


(** Auxiliary notions for 2-cell Horizontal Composition functor *)

(* composable pairs of morphisms as a set *)
Record GenComp T (h: T -> T -> U) := GC {
   h_one : T;
   h_two : T ;
   h_three : T;
   h_first : h h_one h_two ;
   h_second : h h_two h_three }.

(* composable pairs of horizontal morphisms as a set *)
HB.tag Definition HCompSet (C: cquiver) := GenComp (@hhom C).

(* smart projections *)
Definition H2First (C: cquiver) (X: @HCompSet C) : HHomSet C :=
    @HO C _ (h_one X) (h_two X) (h_first X).
Definition H2Second (C: cquiver) (X: @HCompSet C) : HHomSet C :=
    @HO C _ (h_two X) (h_three X) (h_second X).


(* horizontal composition functor: D1 * D1 -> D1 *)
Definition hhcomp (T: hprecat) (x: HCompSet T) : HHomSet T := 
  match x with 
    @GC _ _ a b c h1 h2 => @HO T (@hhom T) a c
                             (@comp (transpose T) a b c h1 h2) end.
HB.tag Definition HComp (C: hprecat) :=
  fun (x: HCompSet C) => @hhcomp C x. 

(* hhunit - horizontal unit functor.

   hhcomp - horizontal composition functor (horizontal composition of
   two horizontal morphisms from a cell product).

   Both specified as object-level functions (they actually come for
   free from the H-D0 category, since we are in the strict case), to
   be lifted by functoriality to morphism-level ones.

   At the object level, hhunit gives a horizontal identity morphism
   for each D0 object. At the morphism level, it gives horizontal
   2-cell identity for each vertical morphism.
  
   In the case of hhcomp, relying on functoriality requires some care
   in defining the product category, making sure that adjacency at the
   object-level (between horizontal morphisms) is matched by adjacency
   at the morphism-level (between 2-cells).  *)


(** Source and target functors *)

(* source prefunctor. 
   HHomSet T is the quiver of the 2-morphisms, thanks to CQuiver. 
   T is the quiver of 1-morphisms. *)
Unset Universe Checking.
#[wrapper]
HB.mixin Record IsSPreFunctor T of VDCat T := {
    is_sprefunctor : IsPreFunctor (HHomSet T) T (@HSource T) }.
HB.structure Definition SPreFunctor : Set := {C of IsSPreFunctor C}.
Set Universe Checking.

(* target prefunctor. *)
Unset Universe Checking.
#[wrapper]
  HB.mixin Record IsTPreFunctor T of VDCat T := {
    is_tprefunctor : IsPreFunctor (HHomSet T) T (@HTarget T) }.
HB.structure Definition TPreFunctor : Set := {C of IsTPreFunctor C}.
Set Universe Checking.

(* source functor. *)
Unset Universe Checking.
#[wrapper]
  HB.mixin Record SPreFunctor_IsFunctor T of SPreFunctor T := {
    is_sfunctor : PreFunctor_IsFunctor (HHomSet T) T (@HSource T) }.
HB.structure Definition SFunctor : Set := {C of SPreFunctor_IsFunctor C}.
Set Universe Checking.

(* target functor. *)
Unset Universe Checking.
#[wrapper]
HB.mixin Record TPreFunctor_IsFunctor T of TPreFunctor T := {
    is_tfunctor : PreFunctor_IsFunctor (HHomSet T) T (@HTarget T) }.
HB.structure Definition TFunctor : Set := {C of TPreFunctor_IsFunctor C}.
Set Universe Checking.


(** Unit functor *)

(* unit prefunctor. *)
Unset Universe Checking.
#[wrapper] 
HB.mixin Record IsUPreFunctor T of NDCat T := 
  { is_uprefunctor : IsPreFunctor T (HHomSet T) (@HUnit T) }.
HB.structure Definition UPreFunctor : Set := {C of IsUPreFunctor C}.
Set Universe Checking.

(* unit functor. *)
Unset Universe Checking.
#[wrapper] 
HB.mixin Record UPreFunctor_IsFunctor T of UPreFunctor T := {
    is_ufunctor : PreFunctor_IsFunctor T (HHomSet T) (@HUnit T) }.
HB.structure Definition UFunctor : Set := {C of UPreFunctor_IsFunctor C}.
Set Universe Checking.

Unset Universe Checking.
HB.structure Definition STUFunctor : Set :=
  {C of SFunctor C & TFunctor C & UFunctor C}.
Set Universe Checking.


(** Lifting of Source, Target and Unit functors to D1 morphisms *)

(* 2-cell source *)
Definition HC2Source (T: SFunctor.type) (a b: @HHomSet T)
  (m: @c2hom T a b) :
  @hom T (HSource a) (HSource b) := @Fhom _ _ (@HSource T) a b m. 

(* 2-cell target *)
Definition HC2Target (T: TFunctor.type) (a b: @HHomSet T)
  (m: @c2hom T a b) :
  @hom T (HTarget a) (HTarget b) := @Fhom _ _ (@HTarget T) a b m. 

(* horizontal 2-cell unit (maps vertical morphisms to horizontally
   unitary 2-cells) *)
Definition HC2Unit (T: UFunctor.type) (a b: T) (m: @hom T a b) :
  c2hom (HUnit a) (HUnit b) := @Fhom _ _ (@HUnit T) a b m. 


(** Horizontal product category (D1 *d0 D1) *)
(* HCompSet T is the pseudo-pullback category used to deal with
    products of D1 (where the adjacency condition is expressed
    w.r.t. D0 *)

(* horizontal composition of two (naked) horizontal morphisms *)
Definition l_hcomp (T: NDCat.type) (a0 a1 a2: T)
  (h0: hhom a0 a1) (h1: hhom a1 a2) : HHomSet T :=
  @HO T _ a0 a2 (@comp (transpose T) a0 a1 a2 h0 h1).

Notation "'sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'sigma' '/ ' x .. y , '/ ' p ']'")
  : type_scope.

(** HCompSet quiver *)
Definition HComp_hom (T: STUFunctor.type) (x y: HCompSet T) :=
   sigma (hh0: C2Hom (h_first x) (h_first y))  
         (hh1: C2Hom (h_second x) (h_second y)), 
         HC2Target hh0 = HC2Source hh1.

HB.instance Definition HCompQuiver (T: STUFunctor.type) :
  IsQuiver (HCompSet T) :=
  IsQuiver.Build (HCompSet T) (fun A B => @HComp_hom T A B).


(** Product precategory *)

Lemma HComp_id_eq (T : STUFunctor.type) (a: HCompSet T) :
  HC2Target (@idmap (@HHomSet T) (H2First a)) =
              HC2Source (@idmap (@HHomSet T) (H2Second a)).
unfold HC2Target, HTarget.
unfold HC2Source, HSource.
repeat rewrite F1; auto.
Defined.

(* HCompSet identity *)
Definition HComp_id (T: STUFunctor.type) (A: HCompSet T) : A ~> A  :=
  let h0 := h_first A
  in let h1 := h_second A
  in let uu0 := @idmap (HHomSet T) (HO h0)
  in let uu1 := @idmap (HHomSet T) (HO h1)
  in @existT (C2Hom h0 h0)
    (fun hh0: (C2Hom h0 h0) =>
       sigma (hh1 : C2Hom h1 h1), HC2Target hh0 = HC2Source hh1) uu0
    (@existT (C2Hom h1 h1)
       (fun hh1: (C2Hom h1 h1) => HC2Target uu0 = HC2Source hh1) uu1
         (@HComp_id_eq T A)).

Definition HComp_comp_auxA (T : STUFunctor.type)
  (A B C : HCompSet T)
  (hhA0 : C2Hom (h_first A) (h_first B))
  (hhA1 : C2Hom (h_second A) (h_second B))
  (ppA : HC2Target hhA0 = HC2Source hhA1)
  (hhB0 : C2Hom (h_first B) (h_first C))
  (hhB1 : C2Hom (h_second B) (h_second C))
  (ppB : HC2Target hhB0 = HC2Source hhB1) :  
  comp (HC2Target hhA0) (HC2Target hhB0) =
  comp (HC2Source hhA1) (HC2Source hhB1).
  rewrite ppA.
  rewrite ppB.
  reflexivity.
Defined.

Definition HComp_comp_auxS (T : STUFunctor.type)
  (A B C : HCompSet T)
  (hhA0 : C2Hom (h_first A) (h_first B))
  (hhA1 : C2Hom (h_second A) (h_second B))
  (ppA : HC2Target hhA0 = HC2Source hhA1)
  (hhB0 : C2Hom (h_first B) (h_first C))
  (hhB1 : C2Hom (h_second B) (h_second C))
  (ppB : HC2Target hhB0 = HC2Source hhB1) :
  HC2Source (comp hhA1 hhB1) = comp (HC2Source hhA1) (HC2Source hhB1). 
  unfold HC2Source, HSource.
  repeat rewrite Fcomp.
  reflexivity.
Defined.

Definition HComp_comp_auxT (T : STUFunctor.type)
  (A B C : HCompSet T)
  (hhA0 : C2Hom (h_first A) (h_first B))
  (hhA1 : C2Hom (h_second A) (h_second B))
  (ppA : HC2Target hhA0 = HC2Source hhA1)
  (hhB0 : C2Hom (h_first B) (h_first C))
  (hhB1 : C2Hom (h_second B) (h_second C))
  (ppB : HC2Target hhB0 = HC2Source hhB1) :
  HC2Target (comp hhA0 hhB0) = comp (HC2Target hhA0) (HC2Target hhB0).
  unfold HC2Target, HTarget.
  repeat rewrite Fcomp.
  reflexivity.
Defined.

Definition HComp_comp_auxI (T : STUFunctor.type)
  (A B C : HCompSet T)
  (hhA0 : C2Hom (h_first A) (h_first B))
  (hhA1 : C2Hom (h_second A) (h_second B))
  (ppA : HC2Target hhA0 = HC2Source hhA1)
  (hhB0 : C2Hom (h_first B) (h_first C))
  (hhB1 : C2Hom (h_second B) (h_second C))
  (ppB : HC2Target hhB0 = HC2Source hhB1) :
  A ~> C.
  econstructor 1 with (comp hhA0 hhB0).
  econstructor 1 with (comp hhA1 hhB1).
  setoid_rewrite HComp_comp_auxS; eauto.
  setoid_rewrite HComp_comp_auxT; eauto.
  eapply HComp_comp_auxA; eauto.
Defined.  
  
(* HCompSet composition, defined in proof mode *)
Definition HComp_comp (T: STUFunctor.type) (A B C: HCompSet T) 
  (chA: A ~> B) (chB: B ~> C) : A ~> C.
  destruct chA as [hhA0 pA].
  destruct chB as [hhB0 pB].
  destruct pA as [hhA1 ppA].
  destruct pB as [hhB1 ppB].
  eapply HComp_comp_auxI; eauto.
Defined.

(* HCompSet is a precategory *)
HB.instance Definition HCompPreCat (T: STUFunctor.type) :
  Quiver_IsPreCat (HCompSet T) := 
  Quiver_IsPreCat.Build (HCompSet T)
                        (@HComp_id T) (@HComp_comp T).


(** Product category *)

Lemma HComp_LeftUnit_lemma (T : STUFunctor.type) :
  forall (a b : HCompSet T) (f : a ~> b), idmap \; f = f.
  intros.
  destruct f.
  destruct s.
  simpl in *. 
  unfold idmap; simpl.
  unfold HComp_id; simpl.
  unfold comp; simpl.
  unfold HComp_comp_auxI; simpl.
   
  assert (idmap \; x = x) as A.
  { rewrite comp1o; auto. }

  assert (idmap \; x0 = x0) as A0.
  { rewrite comp1o; auto. }

  assert (HC2Target (idmap \; x) = HC2Source (idmap \; x0)) as B.
  { rewrite A.
    rewrite A0; auto. }

  destruct a eqn: aaa.
  destruct b eqn: bbb.
  simpl.
 
  assert (existT
    (fun hh0 : C2Hom h_first0 h_first1 =>
       sigma hh1 : C2Hom h_second0 h_second1,HC2Target hh0 = HC2Source hh1)
    (idmap \; x)
    (existT
       (fun hh1 : C2Hom h_second0 h_second1 =>
          HC2Target (idmap \; x) = HC2Source hh1)
       (idmap \; x0)
       B) =
  existT
    (fun hh0 : C2Hom h_first0 h_first1 =>
       sigma hh1 : C2Hom h_second0 h_second1,HC2Target hh0 = HC2Source hh1)
    x
    (existT
       (fun hh1 : C2Hom h_second0 h_second1 => HC2Target x = HC2Source hh1)
       x0
       e)) as C.

  revert B.
  revert A.
  revert A0.
  generalize (idmap \; x) as v.
  generalize (idmap \; x0) as v0.
  intros v0 v A0.
  rewrite A0.
  intro A.
  rewrite A.
  intro B.

  assert (B = e) as BE.
  { eapply Prop_irrelevance. }

  rewrite BE.
  reflexivity.

  inversion aaa; subst.

  assert ((Morphisms.trans_sym_co_inv_impl_morphism
          (RelationClasses.Equivalence_PER RelationClasses.eq_equivalence)
          (HC2Source (idmap \; x0)) (HC2Source idmap \; HC2Source x0)
          (HComp_comp_auxS
             (HComp_id_eq
                {|
                  h_one := h_one0;
                  h_two := h_two0;
                  h_three := h_three0;
                  h_first := h_first0;
                  h_second := h_second0
                |}) e)
          (Morphisms.trans_co_eq_inv_impl_morphism
             RelationClasses.eq_Transitive (HC2Target (idmap \; x))
             (HC2Target idmap \; HC2Target x)
             (HComp_comp_auxT
                (HComp_id_eq
                   {|
                     h_one := h_one0;
                     h_two := h_two0;
                     h_three := h_three0;
                     h_first := h_first0;
                     h_second := h_second0
                   |}) e) (HC2Source idmap \; HC2Source x0)
             (HC2Source idmap \; HC2Source x0)
             (Morphisms.eq_proper_proxy (HC2Source idmap \; HC2Source x0))
             (HComp_comp_auxA
                (HComp_id_eq
                   {|
                     h_one := h_one0;
                     h_two := h_two0;
                     h_three := h_three0;
                     h_first := h_first0;
                     h_second := h_second0
                   |}) e))) = B) as BM.
  { eapply Prop_irrelevance. }
  rewrite BM.
  eapply C.
Qed.  

Lemma HComp_RightUnit_lemma (T : STUFunctor.type) :
  forall (a b : HCompSet T) (f : a ~> b), f \; idmap = f.
  intros.
  destruct f.
  destruct s.
  simpl in *. 
  unfold idmap; simpl.
  unfold HComp_id; simpl.
  unfold comp; simpl.
  unfold HComp_comp_auxI; simpl.
   
  assert (x \; idmap = x) as A.
  { rewrite compo1; auto. }

  assert (x0 \; idmap = x0) as A0.
  { rewrite compo1; auto. }

  assert (HC2Target (x \; idmap) = HC2Source (x0 \; idmap)) as B.
  { rewrite A.
    rewrite A0; auto. }

  destruct a eqn: aaa.
  destruct b eqn: bbb.
  simpl.
 
  assert (existT
    (fun hh0 : C2Hom h_first0 h_first1 =>
       sigma hh1 : C2Hom h_second0 h_second1,
         HC2Target hh0 = HC2Source hh1)
    (x \; idmap)
    (existT
       (fun hh1 : C2Hom h_second0 h_second1 =>
          HC2Target (x \; idmap) = HC2Source hh1)
       (x0 \; idmap)
       B) =
  existT
    (fun hh0 : C2Hom h_first0 h_first1 =>
       sigma hh1 : C2Hom h_second0 h_second1,
         HC2Target hh0 = HC2Source hh1)
    x
    (existT
       (fun hh1 : C2Hom h_second0 h_second1 =>
          HC2Target x = HC2Source hh1)
       x0
       e)) as C.

  revert B.
  revert A.
  revert A0.
  generalize (x \; idmap) as v.
  generalize (x0 \; idmap) as v0.
  intros v0 v A0.
  rewrite A0.
  intro A.
  rewrite A.
  intro B.

  assert (B = e) as BE.
  { eapply Prop_irrelevance. }

  rewrite BE.
  reflexivity.

  inversion aaa; subst.

  assert ((Morphisms.trans_sym_co_inv_impl_morphism
          (RelationClasses.Equivalence_PER RelationClasses.eq_equivalence)
          (HC2Source (x0 \; idmap)) (HC2Source x0 \; HC2Source idmap)
          (HComp_comp_auxS e
             (HComp_id_eq
                {|
                  h_one := h_one1;
                  h_two := h_two1;
                  h_three := h_three1;
                  h_first := h_first1;
                  h_second := h_second1
                |}))
          (Morphisms.trans_co_eq_inv_impl_morphism
             RelationClasses.eq_Transitive (HC2Target (x \; idmap))
             (HC2Target x \; HC2Target idmap)
             (HComp_comp_auxT e
                (HComp_id_eq
                   {|
                     h_one := h_one1;
                     h_two := h_two1;
                     h_three := h_three1;
                     h_first := h_first1;
                     h_second := h_second1
                   |})) (HC2Source x0 \; HC2Source idmap)
             (HC2Source x0 \; HC2Source idmap)
             (Morphisms.eq_proper_proxy (HC2Source x0 \; HC2Source idmap))
             (HComp_comp_auxA e
                (HComp_id_eq
                   {|
                     h_one := h_one1;
                     h_two := h_two1;
                     h_three := h_three1;
                     h_first := h_first1;
                     h_second := h_second1
                   |})))) = B) as BM. 
  { eapply Prop_irrelevance. }
  rewrite BM.
  eapply C.
Qed.  

Lemma HComp_Assoc_lemma (T : STUFunctor.type) :
  forall (a b c d : HCompSet T) (f : a ~> b) (g : b ~> c) (h : c ~> d),
  f \; g \; h = (f \; g) \; h.
  intros.
  remember f as f1.
  remember g as g1.
  remember h as h1.
  destruct f as [x0 s0].
  destruct g as [x1 s1].
  destruct h as [x2 s2].
  destruct s0 as [y0 e0].
  destruct s1 as [y1 e1].
  destruct s2 as [y2 e2].
  simpl.

  set (x01 := comp x0 x1).
  set (x12 := comp x1 x2).
  set (x0_12 := comp x0 x12).
  set (x01_2 := comp x01 x2).
  set (y01 := comp y0 y1).
  set (y12 := comp y1 y2).
  set (y0_12 := comp y0 y12).
  set (y01_2 := comp y01 y2).

  assert (x0_12 = x01_2) as X0.
  { subst x0_12 x01_2.
    rewrite compoA; eauto. }
  assert (y0_12 = y01_2) as Y0.
  { subst y0_12 y01_2.
    rewrite compoA; eauto. }

  set (x01_t := comp (HC2Target x0) (HC2Target x1)).  
  set (x01_2_t := comp x01_t (HC2Target x2)).  
  set (x12_t := comp (HC2Target x1) (HC2Target x2)).  
  set (x0_12_t := comp (HC2Target x0) x12_t).  
  set (y01_s := comp (HC2Source y0) (HC2Source y1)).  
  set (y01_2_s := comp y01_s (HC2Source y2)).  
  set (y12_s := comp (HC2Source y1) (HC2Source y2)).  
  set (y0_12_s := comp (HC2Source y0) y12_s).  

  assert (x01_t = y01_s) as E01.
  { subst x01_t y01_s.
    rewrite e0.
    rewrite e1; auto. }
  assert (x01_2_t = y01_2_s) as E01_2.
  { subst x01_2_t y01_2_s.
    rewrite E01.
    rewrite e2; auto. }
  assert (x12_t = y12_s) as E12.
  { subst x12_t y12_s.
    rewrite e1.
    rewrite e2; auto. }
  assert (x0_12_t = y0_12_s) as E0_12.
  { subst x0_12_t y0_12_s.
    rewrite E12.
    rewrite e0; auto. }

  assert (x0_12_t = x01_2_t) as E02T.
  { subst x0_12_t x01_2_t.
    subst x12_t x01_t.
    rewrite compoA; auto. }
  assert (y0_12_s = y01_2_s) as E02S.
  { subst y0_12_s y01_2_s.
    subst y12_s y01_s.
    rewrite compoA; auto. }
  
  unfold comp.
  simpl.
  unfold HComp_comp.
  simpl.
  inversion Heqf1; subst.
  clear H.

  unfold HComp_comp_auxI; simpl.

  assert (HC2Target (x0 \; x1 \; x2) =
            HC2Source (y0 \; y1 \; y2)) as KR.
  { subst x0_12_t y0_12_s.
    subst x12_t y12_s.
    unfold HC2Target.
    repeat rewrite Fcomp; simpl.
    unfold HC2Target in E0_12.
    rewrite E0_12.
    unfold HC2Source.
    repeat rewrite Fcomp; simpl.
    auto.
  }  

  assert (HC2Target ((x0 \; x1) \; x2) =
            HC2Source ((y0 \; y1) \; y2)) as KL.
  { subst x01_2_t y01_2_s.
    subst x01_t y01_s.
    unfold HC2Target.
    repeat rewrite Fcomp; simpl.
    unfold HC2Target in E01_2.
    rewrite E01_2.
    unfold HC2Source.
    repeat rewrite Fcomp; simpl.
    auto.
  }  
  
  assert (existT
    (fun hh0 : C2Hom (h_first a) (h_first d) =>
     sigma hh1 : C2Hom (h_second a) (h_second d),
         HC2Target hh0 = HC2Source hh1)
    (x0 \; x1 \; x2)
    (existT
       (fun hh1 : C2Hom (h_second a) (h_second d) =>
            HC2Target (x0 \; x1 \; x2) = HC2Source hh1) 
       (y0 \; y1 \; y2)
       KR) 
          =
  existT
    (fun hh0 : C2Hom (h_first a) (h_first d) =>
     sigma hh1 : C2Hom (h_second a) (h_second d),
         HC2Target hh0 = HC2Source hh1)
    ((x0 \; x1) \; x2)
    (existT
       (fun hh1 : C2Hom (h_second a) (h_second d) =>
           HC2Target ((x0 \; x1) \; x2) = HC2Source hh1) 
       ((y0 \; y1) \; y2)
       KL)) as KA.
  { revert KL.
    revert KR.
    subst x0_12 x01_2 x12 x01.
    subst y0_12 y01_2 y12 y01.
    rewrite <- X0.
    rewrite <- Y0.
    intros KR KL.
  
    assert (KR = KL) as I1.
    { eapply Prop_irrelevance. }
    rewrite I1.
    reflexivity.
  }

  assert (Morphisms.trans_sym_co_inv_impl_morphism
          (RelationClasses.Equivalence_PER RelationClasses.eq_equivalence)
          (HC2Source (y0 \; y1 \; y2))
          (HC2Source y0 \; HC2Source (y1 \; y2))
          (HComp_comp_auxS e0
             (Morphisms.trans_sym_co_inv_impl_morphism
                (RelationClasses.Equivalence_PER
                   RelationClasses.eq_equivalence) 
                (HC2Source (y1 \; y2)) (HC2Source y1 \; HC2Source y2)
                (HComp_comp_auxS e1 e2)
                (Morphisms.trans_co_eq_inv_impl_morphism
                   RelationClasses.eq_Transitive (HC2Target (x1 \; x2))
                   (HC2Target x1 \; HC2Target x2) 
                   (HComp_comp_auxT e1 e2) (HC2Source y1 \; HC2Source y2)
                   (HC2Source y1 \; HC2Source y2)
                   (Morphisms.eq_proper_proxy (HC2Source y1 \; HC2Source y2))
                   (HComp_comp_auxA e1 e2))))
          (Morphisms.trans_co_eq_inv_impl_morphism
             RelationClasses.eq_Transitive (HC2Target (x0 \; x1 \; x2))
             (HC2Target x0 \; HC2Target (x1 \; x2))
             (HComp_comp_auxT e0
                (Morphisms.trans_sym_co_inv_impl_morphism
                   (RelationClasses.Equivalence_PER
                      RelationClasses.eq_equivalence) 
                   (HC2Source (y1 \; y2)) (HC2Source y1 \; HC2Source y2)
                   (HComp_comp_auxS e1 e2)
                   (Morphisms.trans_co_eq_inv_impl_morphism
                      RelationClasses.eq_Transitive 
                      (HC2Target (x1 \; x2)) (HC2Target x1 \; HC2Target x2)
                      (HComp_comp_auxT e1 e2) (HC2Source y1 \; HC2Source y2)
                      (HC2Source y1 \; HC2Source y2)
                      (Morphisms.eq_proper_proxy
                         (HC2Source y1 \; HC2Source y2))
                      (HComp_comp_auxA e1 e2))))
             (HC2Source y0 \; HC2Source (y1 \; y2))
             (HC2Source y0 \; HC2Source (y1 \; y2))
             (Morphisms.eq_proper_proxy
                (HC2Source y0 \; HC2Source (y1 \; y2)))
             (HComp_comp_auxA e0
                (Morphisms.trans_sym_co_inv_impl_morphism
                   (RelationClasses.Equivalence_PER
                      RelationClasses.eq_equivalence) 
                   (HC2Source (y1 \; y2)) (HC2Source y1 \; HC2Source y2)
                   (HComp_comp_auxS e1 e2)
                   (Morphisms.trans_co_eq_inv_impl_morphism
                      RelationClasses.eq_Transitive 
                      (HC2Target (x1 \; x2)) (HC2Target x1 \; HC2Target x2)
                      (HComp_comp_auxT e1 e2) (HC2Source y1 \; HC2Source y2)
                      (HC2Source y1 \; HC2Source y2)
                      (Morphisms.eq_proper_proxy
                         (HC2Source y1 \; HC2Source y2))
                      (HComp_comp_auxA e1 e2))))) = KR) as HR.
  { eapply Prop_irrelevance. }

  rewrite HR.
  
  assert (Morphisms.trans_sym_co_inv_impl_morphism
          (RelationClasses.Equivalence_PER RelationClasses.eq_equivalence)
          (HC2Source ((y0 \; y1) \; y2))
          (HC2Source (y0 \; y1) \; HC2Source y2)
          (HComp_comp_auxS
             (Morphisms.trans_sym_co_inv_impl_morphism
                (RelationClasses.Equivalence_PER
                   RelationClasses.eq_equivalence) 
                (HC2Source (y0 \; y1)) (HC2Source y0 \; HC2Source y1)
                (HComp_comp_auxS e0 e1)
                (Morphisms.trans_co_eq_inv_impl_morphism
                   RelationClasses.eq_Transitive (HC2Target (x0 \; x1))
                   (HC2Target x0 \; HC2Target x1) 
                   (HComp_comp_auxT e0 e1) (HC2Source y0 \; HC2Source y1)
                   (HC2Source y0 \; HC2Source y1)
                   (Morphisms.eq_proper_proxy (HC2Source y0 \; HC2Source y1))
                   (HComp_comp_auxA e0 e1))) e2)
          (Morphisms.trans_co_eq_inv_impl_morphism
             RelationClasses.eq_Transitive (HC2Target ((x0 \; x1) \; x2))
             (HC2Target (x0 \; x1) \; HC2Target x2)
             (HComp_comp_auxT
                (Morphisms.trans_sym_co_inv_impl_morphism
                   (RelationClasses.Equivalence_PER
                      RelationClasses.eq_equivalence) 
                   (HC2Source (y0 \; y1)) (HC2Source y0 \; HC2Source y1)
                   (HComp_comp_auxS e0 e1)
                   (Morphisms.trans_co_eq_inv_impl_morphism
                      RelationClasses.eq_Transitive 
                      (HC2Target (x0 \; x1)) (HC2Target x0 \; HC2Target x1)
                      (HComp_comp_auxT e0 e1) (HC2Source y0 \; HC2Source y1)
                      (HC2Source y0 \; HC2Source y1)
                      (Morphisms.eq_proper_proxy
                         (HC2Source y0 \; HC2Source y1))
                      (HComp_comp_auxA e0 e1))) e2)
             (HC2Source (y0 \; y1) \; HC2Source y2)
             (HC2Source (y0 \; y1) \; HC2Source y2)
             (Morphisms.eq_proper_proxy
                (HC2Source (y0 \; y1) \; HC2Source y2))
             (HComp_comp_auxA
                (Morphisms.trans_sym_co_inv_impl_morphism
                   (RelationClasses.Equivalence_PER
                      RelationClasses.eq_equivalence) 
                   (HC2Source (y0 \; y1)) (HC2Source y0 \; HC2Source y1)
                   (HComp_comp_auxS e0 e1)
                   (Morphisms.trans_co_eq_inv_impl_morphism
                      RelationClasses.eq_Transitive 
                      (HC2Target (x0 \; x1)) (HC2Target x0 \; HC2Target x1)
                      (HComp_comp_auxT e0 e1) (HC2Source y0 \; HC2Source y1)
                      (HC2Source y0 \; HC2Source y1)
                      (Morphisms.eq_proper_proxy
                         (HC2Source y0 \; HC2Source y1))
                      (HComp_comp_auxA e0 e1))) e2)) = KL) as HL.
  { eapply Prop_irrelevance. }

  rewrite HL.

  eapply KA.
Qed.

Program Definition HCompCatP (T: STUFunctor.type) :
                                 PreCat_IsCat (HCompSet T).
econstructor.
eapply HComp_LeftUnit_lemma; eauto.
eapply HComp_RightUnit_lemma; eauto.
eapply HComp_Assoc_lemma; eauto.
Qed.

(* HCompSet is a category *)
HB.instance Definition HCompCat (T: STUFunctor.type) := HCompCatP T.


(** Horizontal composition functor and strict double categories *)

(* composition prefunctor *)
Unset Universe Checking.
#[wrapper] 
HB.mixin Record IsCPreFunctor T of STUFunctor T :=
  { is_cprefunctor : IsPreFunctor (HCompSet T) (HHomSet T) (@HComp T) }.
HB.structure Definition CPreFunctor : Set := {C of IsCPreFunctor C}.
Set Universe Checking.

(* composition functor - gives the definition of Strict Double Category *)
Unset Universe Checking.
#[wrapper] 
HB.mixin Record CPreFunctor_IsFunctor T of CPreFunctor T := {
    is_cfunctor : PreFunctor_IsFunctor (HCompSet T) (HHomSet T) (@HComp T) }.
#[short(type="dcat")]
HB.structure Definition DCat : Set := {C of CPreFunctor_IsFunctor C}.
Set Universe Checking.

(* horizontal 2-cell composition: maps two adjecent pairs of
   horizontal morphisms (a and b) and a pullback-category morphism
   between them (m, which basically gives two adjecent cells) to a
   2-cell morphism between the horizontal composition (HComp) of each
   pair *)
Definition HC2Comp (T: DCat.type) (a b: HCompSet T)
  (m: @hom (HCompSet T) a b) :
  c2hom (HComp a) (HComp b) := @Fhom _ _ (@HComp T) a b m.

Program Definition HC2Comp_flat (T: DCat.type) (a0 a1 a2 b0 b1 b2: T)
  (h0: hhom a0 a1) (h1: hhom a1 a2)
  (k0: hhom b0 b1) (k1: hhom b1 b2)
  (hh0: C2Hom h0 k0)
  (hh1: C2Hom h1 k1)
  (k: HC2Target hh0 = HC2Source hh1)
  :   (* C2Hom (hcomp _ _ _ h0 h1) (hcomp _ _ _ k0 k1) *)
  c2hom (l_hcomp h0 h1) (l_hcomp k0 k1) :=
  @Fhom _ _ (@HComp T) (GC h0 h1) (GC k0 k1) _.
Obligation 1.
refine (@existT (C2Hom h0 k0) _ hh0 (@existT (C2Hom h1 k1) _ hh1 k)).
Defined.

(********************************************************************)
(********************************************************************)


Section th_of_pb.
Variables (Q : cat) (A B C D E F : Q).
Variables (f : A ~> D) (g : B ~> D) (h : C ~> A).
Variables (u : E ~> A) (v : E ~> B) (w : F ~> C) (z : F ~> E).
Variable (uvfg : pbsquare u v f g).

Set Printing Width 50.
Theorem pbsquarec_compP :
  pbsquare w z h u <=> pbsquare w (z \; v) (h \; f) g.
Proof.
split=> [] sq.

  have @sq_ispb : pullback (Cospan h u) := HB.pack (Span w z) sq.
  have @uvfg_ispb : pullback (Cospan f g) := HB.pack (Span u v) uvfg.
  have /=E2 := @is_square _ _ _ _ sq_ispb.
  have /=E1 := @is_square _ _ _ _ uvfg_ispb.

  have p1 : @isPrePullback Q C B (Cospan (h \; f) g) (Span w (z \; v)).
    by constructor; rewrite /= compoA E2 -compoA E1 compoA.
  pose big_black_square : prepullback (Cospan (h \; f) g) :=
    HB.pack (Span w (z \; v)) p1.

  have @from : forall
    (big_red_square : prepullback {| top := D; left2top := h \; f; right2top := g |}),
    big_red_square ~> pb_terminal big_black_square.

    move=> big_red_square; unfold pb_terminal.

    have /= := @is_square _ _ _ _ big_red_square.

    pose F' := bot big_red_square.
    set w' : F' ~> C := bot2left big_red_square.
    set z' : F' ~> B := bot2right big_red_square.
    move=> E3.
    
    have xxx : isPrePullback Q A B (Cospan f g) (Span (w' \; h) z').
      by constructor=> /=; rewrite -compoA E3.
    pose red_black_square : prepullback (Cospan f g) :=
      HB.pack (Span (w' \; h) z') xxx.
    have  := @from_unique _ (pb_terminal uvfg_ispb) red_black_square.
    set blue := @from _ (pb_terminal uvfg_ispb) red_black_square.
    move=> blue_unique.

    have p3 : @isPrePullback Q C E (Cospan h u) (Span w' (bot_map blue)).
      by constructor; rewrite /= (bot2left_map blue). (* buggy unifier without blue *)
    pose blue_red_black_square : prepullback (Cospan h u) :=
      HB.pack (Span w' (bot_map blue)) p3.

    pose red := @from _ (pb_terminal sq_ispb) blue_red_black_square.

    admit.



  have p2 : prepullback_isTerminal.axioms_ Q C B  (Cospan (h \; f) g) (Span w (z \; v)) p1.
    constructor. econstructor=> /=.
    admit.

    by HB.from p1 p2.

Admitted.

End th_of_pb.


Module test.

Section test.
Variables (Q : precat) (A B : Q) (c : cospan A B).
Variable (p : pullback c).
Check pb_terminal p : terminal _.

End test.
End test.




