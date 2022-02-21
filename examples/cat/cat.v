Require Import ssreflect ssrfun.
From HB Require Import structures.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Add Search Blacklist "__canonical__".

Declare Scope cat_scope.
Delimit Scope cat_scope with cat.
Local Open Scope cat_scope.

Axiom funext : forall {T : Type} {U : T -> Type} [f g : forall t, U t],
  (forall t, f t = g t) -> f = g.
Axiom propext : forall P Q : Prop, P <-> Q -> P = Q.
Axiom Prop_irrelevance : forall (P : Prop) (x y : P), x = y.

Definition U := Type.
Identity Coercion U_to_type : U >-> Sortclass.

HB.mixin Record HasHom C := { hom : C -> C -> U }.
Unset Universe Checking.
HB.structure Definition Hom : Set := { C of HasHom C }.
Set Universe Checking.
Notation homType := Hom.type.
Bind Scope cat_scope with Hom.type.
Bind Scope cat_scope with hom.
Arguments hom {C} : rename.
Notation "a ~> b" := (hom a b)
   (at level 99, b at level 200, format "a  ~>  b") : cat_scope.

HB.mixin Record Hom_IsPreCat C of Hom C := {
  idmap : forall (a : C), a ~> a;
  comp : forall (a b c : C), (a ~> b) -> (b ~> c) -> (a ~> c);
}.

HB.factory Record IsPreCat C := {
  hom : C -> C -> U;
  idmap : forall (a : C), hom a a;
  comp : forall (a b c : C), hom a b -> hom b c -> hom a c;
}.
HB.builders Context C of IsPreCat C.
  HB.instance Definition _ := HasHom.Build C hom.
  HB.instance Definition _ := Hom_IsPreCat.Build C idmap comp.
HB.end.

Unset Universe Checking.
HB.structure Definition PreCat : Set := { C of IsPreCat C }.
Set Universe Checking.
Notation precat := PreCat.type.
Bind Scope cat_scope with precat.
Arguments idmap {C} {a} : rename.
Arguments comp {C} {a b c} : rename.

Notation "f \o g" := (comp g f) : cat_scope.
Notation "f \; g" := (comp f g) : cat_scope.
Notation "\idmap_ a" := (@idmap _ a) (only parsing, at level 0) : cat_scope.

HB.mixin Record PreCat_IsCat C of PreCat C := {
  comp1o : forall (a b : C) (f : a ~> b), idmap \; f = f;
  compo1 : forall (a b : C) (f : a ~> b), f \; idmap = f;
  compoA : forall (a b c d : C) (f : a ~> b) (g : b ~> c) (h : c ~> d),
    f \; (g \; h) = (f \; g) \; h
}.
Unset Universe Checking.
HB.structure Definition Cat : Set := { C of PreCat_IsCat C & IsPreCat C }.
Set Universe Checking.
Notation cat := Cat.type.
Arguments compo1 {C a b} : rename.
Arguments comp1o {C a b} : rename.
Arguments compoA {C a b c d} : rename.

Definition discrete (T : Type) := T.
HB.instance Definition _ T := @IsPreCat.Build (discrete T) (fun x y => x = y)
  (fun=> erefl) (@etrans _).
Lemma etransA T (a b c d : discrete T) (f : a ~> b) (g : b ~> c) (h : c ~> d) :
    f \; (g \; h) = (f \; g) \; h.
Proof. by rewrite /idmap/comp/=; case: _ / h; case: _ / g. Qed.
HB.instance Definition _ T := PreCat_IsCat.Build (discrete T) (@etrans_id _)
   (fun _ _ _ => erefl) (@etransA _).

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

HB.mixin Record IsPreFunctor (C D : Hom.type) (F : C -> D) := {
   Fhom_of : forall (a b : C), (a ~> b) -> (F a ~> F b)
}.

Unset Universe Checking.
HB.structure Definition PreFunctor (C D : Hom.type) : Set :=
  { F of IsPreFunctor C D F }.
Set Universe Checking.
HB.instance Definition _ := HasHom.Build Hom.type PreFunctor.type.
Arguments Fhom_of /.

Definition Fhom_phant (C D : Hom.type) (F : C ~> D)
  of phantom (_ -> _) F := @Fhom_of C D F.
Notation "F ^$" := (@Fhom_phant _ _ _ (Phantom (_ -> _) F) _ _)
   (at level 1, format "F ^$") : cat_scope.
Notation "F <$> f" := (@Fhom_phant _ _ _ (Phantom (_ -> _) F) _ _ f)
   (at level 58, format "F  <$>  f", right associativity) : cat_scope.

Lemma prefunctorP (C D : homType) (F G : C ~> D) (eqFG : F =1 G) :
   let homF a b F := F a ~> F b in
   (forall a b f, eq_rect _ (homF a b) (F <$> f) _ (funext eqFG) = G <$> f) ->
  F = G.
Proof.
rewrite !/Fhom_phant/=.
move: F G => [F [[/= Fhom]]] [G [[/= Ghom]]] in eqFG *.
case: _ / (funext eqFG) => /= in Ghom * => eqFGhom.
congr PreFunctor.Pack; congr PreFunctor.Class; congr IsPreFunctor.Axioms_.
by do 3!apply: funext=> ?.
Qed.

HB.mixin Record PreFunctor_IsFunctor (C D : precat) (F : C -> D)
     of @PreFunctor C D F := {
   F1 : forall (a : C), F^$ \idmap_a = \idmap_(F a);
   Fcomp : forall (a b c : C) (f : a ~> b) (g : b ~> c),
      F^$ (f \; g) = F^$ f \; F^$ g;
}.
Unset Universe Checking.
HB.structure Definition Functor (C D : precat) : Set :=
  { F of IsPreFunctor C D F & PreFunctor_IsFunctor C D F }.
Set Universe Checking.
HB.instance Definition _ := HasHom.Build precat Functor.type.
HB.instance Definition _ := HasHom.Build cat Functor.type.

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

HB.instance Definition _ (C : precat) :=
  IsPreFunctor.Build C C idfun (fun a b => idfun).
HB.instance Definition _ (C : precat) :=
  PreFunctor_IsFunctor.Build C C idfun (fun=> erefl) (fun _ _ _ _ _ => erefl).

Section comp_prefunctor.
Context {C D E : homType} {F : C ~> D} {G : D ~> E}.

HB.instance Definition _ := IsPreFunctor.Build C E (G \o F)%FUN
   (fun a b f => G^$ (F^$ f)).
Lemma comp_Fun (a b : C) (f : a ~> b) : (G \o F)%FUN <$> f = G <$> (F <$> f).
Proof. by []. Qed.
End comp_prefunctor.

Section comp_functor.
Context {C D E : precat} {F : C ~> D} {G : D ~> E}.
Lemma comp_F1 (a : C) : (G \o F)%FUN^$ \idmap_a = \idmap_((G \o F)%FUN a).
Proof. by rewrite !comp_Fun !F1. Qed.
Lemma comp_Fcomp  (a b c : C) (f : a ~> b) (g : b ~> c) :
  (G \o F)%FUN^$ (f \; g) = (G \o F)%FUN^$ f \; (G \o F)%FUN^$ g.
Proof. by rewrite !comp_Fun !Fcomp. Qed.
HB.instance Definition _ := PreFunctor_IsFunctor.Build C E (G \o F)%FUN
   comp_F1 comp_Fcomp.
End comp_functor.

HB.instance Definition _ := Hom_IsPreCat.Build precat
  (fun=> idfun) (fun C D E (F : C ~> D) (G : D ~> E) => (G \o F)%FUN).
HB.instance Definition _ := Hom_IsPreCat.Build cat
  (fun=> idfun) (fun C D E (F : C ~> D) (G : D ~> E) => (G \o F)%FUN).

Lemma funext_frefl A B (f : A -> B) : funext (frefl f) = erefl.
Proof. exact: Prop_irrelevance. Qed.

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

HB.mixin Record Hom_IsPreConcrete T of Hom T := {
  concrete : T -> U;
  concrete_fun : forall (a b : T), (a ~> b) -> (concrete a) -> (concrete b);
  (* concrete_fun_inj : forall a b, injective (concrete_fun a b) *)
}.
Unset Universe Checking.
HB.structure Definition PreConcreteHom : Set :=
  { C of Hom_IsPreConcrete C & HasHom C }.
Set Universe Checking.
Coercion concrete : PreConcreteHom.sort >-> U.

HB.mixin Record PreConcrete_IsConcrete T of PreConcreteHom T := {
  concrete_fun_inj : forall (a b : T), injective (concrete_fun a b)
}.
Unset Universe Checking.
HB.structure Definition ConcreteHom : Set :=
  { C of PreConcreteHom C & PreConcrete_IsConcrete C }.
Set Universe Checking.

HB.instance Definition _ (C : ConcreteHom.type) :=
  IsPreFunctor.Build _ _ (concrete : C -> U) concrete_fun.

HB.mixin Record PreCat_IsConcrete T of ConcreteHom T & PreCat T := {
  concrete1 : forall (a : T), concrete <$> \idmap_a = idfun;
  concrete_comp : forall (a b c : T) (f : a ~> b) (g : b ~> c),
    concrete <$> (f \; g) = ((concrete <$> g) \o (concrete <$> f))%FUN;
}.
Unset Universe Checking.
HB.structure Definition ConcretePreCat : Set :=
  { C of PreCat C & ConcreteHom C & PreCat_IsConcrete C }.
HB.structure Definition ConcreteCat : Set :=
  { C of Cat C & ConcreteHom C & PreCat_IsConcrete C }.
Set Universe Checking.

HB.instance Definition _ (C : ConcretePreCat.type) :=
  PreFunctor_IsFunctor.Build C U concrete (@concrete1 _) (@concrete_comp _).
HB.instance Definition _ (C : ConcreteCat.type) :=
  PreFunctor_IsFunctor.Build C U concrete (@concrete1 _) (@concrete_comp _).

HB.instance Definition _ := Hom_IsPreConcrete.Build U (fun _ _ => id).
HB.instance Definition _ := PreConcrete_IsConcrete.Build U (fun _ _ _ _ => id).
HB.instance Definition _ := PreCat_IsConcrete.Build U
   (fun=> erefl) (fun _ _ _ _ _ => erefl).

Unset Universe Checking.
HB.instance Definition _ := Hom_IsPreConcrete.Build homType (fun _ _ => id).
HB.instance Definition _ := Hom_IsPreConcrete.Build precat (fun _ _ => id).
HB.instance Definition _ := Hom_IsPreConcrete.Build cat (fun _ _ => id).
Lemma homType_concrete_subproof : PreConcrete_IsConcrete homType.
Proof.
constructor=> C D F G FG; apply: prefunctorP.
  by move=> x; congr (_ x); apply: FG.
by move=> *; apply: Prop_irrelevance.
Qed.
HB.instance Definition _ := homType_concrete_subproof.

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

Definition cst (C D : homType) (c : C) := fun of D => c.
Arguments cst {C} D c.
HB.instance Definition _ {C D : precat} (c : C) :=
  IsPreFunctor.Build D C (cst D c) (fun _ _ _ => idmap).
HB.instance Definition _ {C D : cat} (c : C) :=
  PreFunctor_IsFunctor.Build D C (cst D c) (fun=> erefl)
    (fun _ _ _ _ _ => esym (compo1 idmap)).

Definition catop (C : Type) : Type := C.
Notation "C ^op" := (catop C) (at level 10, format "C ^op") : cat_scope.
HB.instance Definition _ (C : homType) := HasHom.Build (C^op) (fun a b => hom b a).
HB.instance Definition _ (C : precat) := Hom_IsPreCat.Build (C^op) (fun=> idmap)
   (fun _ _ _ f g => g \; f).
HB.instance Definition _ (C : cat) := PreCat_IsCat.Build (C^op)
   (fun _ _ _ => compo1 _) (fun _ _ _ => comp1o _)
   (fun _ _ _ _ _ _ _ => esym (compoA _ _ _)).

HB.instance Definition _ {C : precat} {c : C} :=
  IsPreFunctor.Build C _ (hom c) (fun a b f g => g \; f).
Lemma hom_Fhom_subproof (C : cat) (x : C) :
  PreFunctor_IsFunctor _ _ (hom x).
Proof. by split=> *; apply/funext => h; [apply: compo1 | apply: compoA]. Qed.
HB.instance Definition _ {C : cat} {c : C} := hom_Fhom_subproof c.

Lemma hom_op {C : homType} (c : C^op) : hom c = (@hom C)^~ c.
Proof. reflexivity. Qed.

Lemma homFhomx {C : precat} (a b c : C) (f : a ~> b) (g : c ~> a) :
  (hom c <$> f) g = g \; f.
Proof. by []. Qed.

Notation "C ~> D :> T" := ((C : T) ~> (D : T))
  (at level 99, D, T at level 200, format "C  ~>  D  :>  T").

Definition dprod {I : Type} (C : I -> Type) := forall i, C i.

Section hom_dprod.
Context {I : Type} (C : I -> Hom.type).
Definition dprod_hom_subdef (a b : dprod C) := forall i, a i ~> b i.
HB.instance Definition _ := HasHom.Build (dprod C) dprod_hom_subdef.
End hom_dprod.
Arguments dprod_hom_subdef /.

Section precat_dprod.
Context {I : Type} (C : I -> precat).
Definition dprod_idmap_subdef (a : dprod C) : a ~> a := fun=> idmap.
Definition dprod_comp_subdef (a b c : dprod C) (f : a ~> b) (g : b ~> c) : a ~> c :=
  fun i => f i \; g i.
HB.instance Definition _ := IsPreCat.Build (dprod C)
   dprod_idmap_subdef dprod_comp_subdef.
End precat_dprod.
Arguments dprod_idmap_subdef /.
Arguments dprod_comp_subdef /.

Section cat_dprod.
Context {I : Type} (C : I -> cat).
Local Notation type := (dprod C).
Lemma dprod_is_cat : PreCat_IsCat type.
Proof.
split=> [a b f|a b f|a b c d f g h]; apply/funext => i;
[exact: comp1o | exact: compo1 | exact: compoA].
Qed.
HB.instance Definition _ := dprod_is_cat.
End cat_dprod.

Section hom_prod.
Context {C D : Hom.type}.
Definition prod_hom_subdef (a b : C * D) := ((a.1 ~> b.1) * (a.2 ~> b.2))%type.
HB.instance Definition _ := HasHom.Build (C * D)%type prod_hom_subdef.
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

HB.mixin Record IsNatural (C D : precat) (F G : C ~> D :> homType)
     (n : forall c, F c ~> G c) := {
   natural : forall (a b : C) (f : a ~> b), F <$> f \; n b = n a \; G <$> f
}.
Unset Universe Checking.
HB.structure Definition Natural (C D : precat)
    (F G : C ~> D :> homType) : Set :=
  { n of @IsNatural C D F G n }.
Set Universe Checking.
HB.instance Definition _  (C D : precat) :=
  HasHom.Build (PreFunctor.type C D) (@Natural.type C D).
HB.instance Definition _  (C D : precat) :=
  HasHom.Build (Functor.type C D) (@Natural.type C D).
Arguments natural {C D F G} n [a b] f : rename.

Lemma naturalx (C : precat) (D : ConcretePreCat.type)
  (F G : C ~> D :> homType) (n : F ~> G)  (a b : C) (f : a ~> b) g :
    (concrete <$> n b) ((concrete <$> F <$> f) g) =
    (concrete <$> G <$> f) ((concrete <$> n a) g).
Proof.
have /(congr1 (fun h  => (concrete <$> h) g)) := natural n f.
by rewrite !Fcomp.
Qed.
Arguments naturalx {C D F G} n [a b] f.

Lemma naturalU (C : precat) (F G : C ~> U :> homType) (n : F ~> G)
   (a b : C) (f : a ~> b) g :  n b (F^$ f g) = G^$ f (n a g).
Proof. exact: (naturalx n). Qed.

Lemma natP (C D : precat) (F G : C ~> D :> homType) (n m : F ~> G) :
  Natural.sort n = Natural.sort m -> n = m.
Proof.
case: n m => [/= n nP] [/= m mP] enm.
elim: _ / enm in mP *; congr Natural.Pack.
case: nP mP => [[?]] [[?]]; congr Natural.Class.
congr IsNatural.Axioms_.
exact: Prop_irrelevance.
Qed.

Notation "F ~~> G" :=
   (F ~> G :> (_ ~> _ :> homType))
  (at level 99, G at level 200, format "F  ~~>  G").
Notation "F ~~> G :> C ~> D" :=
   (F ~> G :> (C ~> D :> homType))
  (at level 99, G at level 200, C, D at level 0, format "F  ~~>  G  :>  C  ~>  D").

Section nat_map_left.
Context {C D E : precat} {F G : C ~> D}.

Definition nat_lmap (H : D ~> E :> homType) (n : forall c, F c ~> G c) :
  forall c, (H \o F)%FUN c ~> (H \o G)%FUN c := fun c => H <$> n c.
Lemma nat_lmap_is_natural (H : D ~> E) (n : F ~~> G) :
  IsNatural C E (H \o F) (H \o G) (nat_lmap H n).
Proof. by constructor=> a b f; rewrite /nat_lmap/= -!Fcomp natural. Qed.
HB.instance Definition _ H n := nat_lmap_is_natural H n.
(* Definition nat_lmap_nat (H : D ~> E) (n : F ~~> G) : H \o F ~~> H \o G := nat_lmap H n. *)
End nat_map_left.

Notation "F <o$> n" := (nat_lmap F n)
   (at level 58, format "F  <o$>  n", right associativity) : cat_scope.

Section nat_map_right.
Context {C D E : precat} {F G : C ~> D}.

Definition nat_rmap (H : E -> C) (n : forall c, F c ~> G c) :
  forall c, (F \o H)%FUN c ~> (G \o H)%FUN c := fun c => n (H c).
Lemma nat_rmap_is_natural (H : E ~> C :> homType) (n : F ~~> G) :
  IsNatural E D (F \o H)%FUN (G \o H)%FUN (nat_rmap H n).
Proof. by constructor=> a b f; rewrite /nat_lmap/= natural. Qed.
HB.instance Definition _ H n := nat_rmap_is_natural H n.

End nat_map_right.

Notation "F <$o> n" := (nat_rmap F n)
   (at level 58, format "F  <$o>  n", right associativity) : cat_scope.

HB.mixin Record IsMonad (C : precat) (M : C -> C) of @PreFunctor C C M := {
  unit : idfun ~~> M;
  join : (M \o M)%FUN ~~> M;
  bind : forall (a b : C), (a ~> M b) -> (M a ~> M b);
  bindE : forall a b (f : a ~> M b), bind a b f = M <$> f \; join b;
  unit_join : forall a, (M <$> unit a) \; join _ = idmap;
  join_unit : forall a, join _ \; (M <$> unit a) = idmap;
  join_square : forall a, M <$> join a \; join _ = join _ \; join _
}.

HB.structure Definition PreMonad (C : precat) :=
   {M of @PreFunctor C C M & IsMonad C M}.
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
HB.structure Definition PreCoMonad (C : precat) :=
   {M of @PreFunctor C C M & IsCoMonad C M}.
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

HB.mixin Record IsRightAdjoint (D C : precat) (R : D -> C)
    of @PreFunctor D C R := {
  L_ : C ~> D;
  phi : forall c d, (L_ c ~> d) -> (c ~> R d);
  psy : forall c d, (c ~> R d) -> (L_ c ~> d);
  phi_psy c d : (phi c d \o psy c d)%FUN = @id (c ~> R d);
  psy_phi c d : (psy c d \o phi c d)%FUN = @id (L_ c ~> d)
}.
HB.structure Definition RightAdjoint (D C : precat) :=
  { R of @Functor D C R & IsRightAdjoint D C R }.
Arguments L_ {_ _}.
Arguments phi {D C s} {c d}.
Arguments psy {D C s} {c d}.

Lemma idFmap (C : cat) (a b : C) (f : a ~> b) : idfun <$> f = f.
Proof. by []. Qed.

Lemma compFmap (C D E : cat) (F : C ~> D) (G : D ~> E) (a b : C) (f : a ~> b) :
  (G \o F) <$> f = G <$> F <$> f.
Proof. by []. Qed.

Section RightAdjointTheory.
Context {D C : cat} (R : RightAdjoint.type D C).
Definition RMonad := (R \o L_ R)%FUN.
Definition RCoMonad := (L_ R \o R)%FUN.

Definition Runit (c : C) : c ~> (R \o L_ R) c := phi idmap.
Lemma Runit_subproof : IsNatural _ _ idfun (R \o L_ R) Runit.
Proof.
constructor => a b f /=.
rewrite /Runit/=.
rewrite idFmap.
rewrite compFmap.

Definition Rjoin (c : C) : ((R \o L_ R) \o (R \o L_ R)) c ~> (R \o L_ R) c :=
  R <$> psy idmap.

Definition Rcounit (d : D) : (L_ R \o R)%FUN d ~> d := psy idmap.
Definition Rcojoin (d : D) : (L_ R \o R)%FUN d ~> ((L_ R \o R) \o (L_ R \o R))%FUN d :=
  L_ R <$> phi idmap.


 phi idmap.

(* HB.instance Definition _ : Monad _ RMonad := Rmonad_subdef. *)
(* HB.instance Definition _ : CoMonad _ RCoMonad := Rcomonad_subdef. *)

(* Lemma phiE c d f : phi c d f = @unit _ RMonad c \; R <$> f. *)
(* Proof. exact: phiE_subproof. Qed. *)

(* Lemma psyE c d f : psy c d f = L_ R <$> f \; @counit _ RCoMonad d. *)
(* Proof. exact: psyE_subproof. Qed. *)

Lemma psy_phi (c : C) (d : D) : (psy c d \o phi c d)%FUN = @id (L_ R c ~> d).
Proof.
apply/funext=> f /=.
rewrite phiE psyE /= Fcomp. 
pose cud := @counit _ RCoMonad d.
pose uc := @unit _ RMonad c.
suff: uc \; (RMonad <$> f) \; R <$> cud = f.
  rewrite /RMonad/=.
  (* rewrite (@comp_Fun _ _ _ (L_ R) R). *)
  rewrite /(_^$)/=.
rewrite /HB_unnamed_mixin_941/=.
rewrite /HB_unnamed_factory_937/=.
rewrite /= in cud *.
  rewrite /
  rewrite /




rewrite 




End RightAdjointTheory.

Section hom_repr.
Context {C : cat} (F : C ~> U :> cat).

Definition homF (c : C) : U := hom c ~~> F.

Section nat.
Context (x y : C) (xy : x ~> y) (n : hom x ~~> F).
Definition homFhom c : hom y c ~> F c := fun g => n _ (xy \; g).

Lemma homFhom_natural_subdef : IsNatural _ _ _ _ homFhom.
Proof.
by split=> a b f /=; apply/funext => g /=;
   rewrite /homFhom !Ucompx/= !naturalU/= Fcomp.
Qed.
HB.instance Definition _ := homFhom_natural_subdef.
End nat.
Arguments homFhom / : clear implicits.

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

Definition repr_hom (fc : F c) a : hom c a ~> F a := fun f => F^$ f fc.
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

Module comma.
Section homcomma.
Context {C D E : precat} (F : C ~> E) (G : D ~> E).

Definition type := { x : C * D & F x.1 ~> G x.2 }.
Definition hom_subdef (a b : type) := {
    f : tag a ~> tag b & F^$ f.1 \; tagged b = tagged a \; G^$ f.2
  }.
HB.instance Definition _ := HasHom.Build type hom_subdef.
End homcomma.
Arguments hom_subdef /.
Section comma.
Context {C D E : cat} (F : C ~> E) (G : D ~> E).
Notation type := (type F G).

Program Definition idmap_subdef (a : type) : a ~> a := @Tagged _ idmap _ _.
Next Obligation. by rewrite !F1 comp1o compo1. Qed.
Program Definition comp_subdef (a b c : type) (f : a ~> b) (g : b ~> c) : a ~> c :=
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

HB.mixin Record PreCat_IsMonoidal C of PreCat C := {
  one : C;
  prod : (C * C)%type ~> C :> precat ;
}.
HB.structure Definition PreMonoidal := { C of PreCat C & PreCat_IsMonoidal C }.
Notation premonoidal := PreMonoidal.type.
Arguments prod {C} : rename.
Notation "a * b" := (prod (a, b)) : cat_scope.
Reserved Notation "f ** g"   (at level 40, g at level 40, format "f  **  g").
Notation "f ** g" := (prod^$ (f, g)) (only printing) : cat_scope.
Notation "f ** g" := (prod^$ ((f, g) : (_, _) ~> (_, _))) (only parsing) : cat_scope.
Notation "1" := one.

Definition hom_cast {C : homType} {a a' : C} (eqa : a = a') {b b' : C} (eqb : b = b') :
  (a ~> b) -> (a' ~> b').
Proof. now elim: _ / eqa; elim: _ / eqb. Defined.


HB.mixin Record PreFunctor_IsMonoidal (C D : premonoidal) F of @PreFunctor C D F := {
  fun_one : F 1 = 1;
  fun_prod : forall (x y : C), F (x * y) = F x * F y;
  (* fun_prodF : forall (x x' : C) (f : x ~> x') (y y' : C) (g : y ~> y'), *)
  (*   hom_cast (fun_prod _ _) (fun_prod _ _) (F^$ (f ** g)) = F^$ f ** F^$ g *)
}.
HB.structure Definition MonoidalPreFunctor C D := { F of @PreFunctor_IsMonoidal C D F }.
Arguments fun_prod {C D F x y} : rename.
(* Arguments fun_prodF {C D F x x'} f {y y'} g : rename. *)
Unset Universe Checking.
HB.instance Definition _ := HasHom.Build premonoidal MonoidalPreFunctor.type.
Set Universe Checking.

(* Definition comma_is_premonoidal (C D E : premonoidal) *)
(*   (F : C ~> E) (G : D ~> E) := F. *)

HB.instance Definition _ (C : Hom.type) :=
  IsPreFunctor.Build (C * C)%type C fst
     (fun (a b : C * C) (f : a ~> b) => f.1).
HB.instance Definition _ (C : Hom.type) :=
  IsPreFunctor.Build (C * C)%type C snd
     (fun (a b : C * C) (f : a ~> b) => f.2).

Definition prod3l {C : PreMonoidal.type} (x : C * C * C) : C :=
  (x.1.1 * x.1.2) * x.2.
HB.instance Definition _ {C : PreMonoidal.type} :=
  IsPreFunctor.Build _ C prod3l
   (fun a b (f : a ~> b) => (f.1.1 ** f.1.2) ** f.2).

Definition prod3r {C : PreMonoidal.type} (x : C * C * C) : C :=
  x.1.1 * (x.1.2 * x.2).
HB.instance Definition _ {C : PreMonoidal.type} :=
  IsPreFunctor.Build _ C prod3r
   (fun a b (f : a ~> b) => f.1.1 ** (f.1.2 ** f.2)).

Definition prod1r {C : PreMonoidal.type} (x : C) : C := 1 * x.
HB.instance Definition _ {C : PreMonoidal.type} :=
  IsPreFunctor.Build C C prod1r
   (fun (a b : C) (f : a ~> b) => \idmap_1 ** f).

Definition prod1l {C : PreMonoidal.type} (x : C) : C := x * 1.
HB.instance Definition _ {C : PreMonoidal.type} :=
  IsPreFunctor.Build C C prod1l
   (fun (a b : C) (f : a ~> b) => f ** \idmap_1).

HB.mixin Record PreMonoidal_IsMonoidal C of PreMonoidal C := {
  prodA  : prod3l ~~> prod3r;
  prod1c : prod1r ~~> idfun;
  prodc1 : prod1l ~~> idfun;
  prodc1c : forall (x y : C),
      prodA (x, 1, y) \; \idmap_x ** prod1c y = prodc1 x ** \idmap_y;
  prodA4 : forall (w x y z : C),
      prodA (w * x, y, z) \; prodA (w, x, y * z) =
        prodA (w, x, y) ** \idmap_z \; prodA (w, x * y, z) \; \idmap_w ** prodA (x, y, z);
}.

Unset Universe Checking.
HB.structure Definition Monoidal : Set :=
  { C of PreMonoidal_IsMonoidal C & PreMonoidal C }.
Set Universe Checking.

