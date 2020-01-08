Require Import String ssreflect ssrfun ssrbool ZArith hb classical.
From elpi Require Import elpi.

Declare Scope hb_scope.
Delimit Scope hb_scope with G.

Local Open Scope classical_set_scope.
Local Open Scope hb_scope.

Module Stage11.

Elpi hb.structure TYPE.

Elpi hb.declare_mixin AddAG_of_TYPE A.
  Record axioms := Axioms {
    zero : A;
    add : A -> A -> A;
    opp : A -> A;
    addrA : associative add;
    addrC : commutative add;
    add0r : left_id zero add;
    addNr : left_inverse zero opp add;
  }.
Elpi hb.end.
Elpi hb.structure AddAG AddAG_of_TYPE.axioms.

(* TODO: command hb.module_export which creates a module,
   exports it immediatly and remembers that it should be
   added to the final Theory module created at file closure *)
Notation "0" := zero : hb_scope.
Infix "+" := (@add _) : hb_scope.
Notation "- x" := (@opp _ x) : hb_scope.
Notation "x - y" := (x + - y) : hb_scope.

(* Theory *)

Section AddAGTheory.
  Variable A : AddAG.type.
  Implicit Type (x : A).

  Lemma addr0 : right_id (@zero A) add.
  Proof. by move=> x; rewrite addrC add0r. Qed.

  Lemma addrN : right_inverse (@zero A) opp add.
  Proof. by move=> x; rewrite addrC addNr. Qed.

  Lemma subrr x : x - x = 0.
  Proof. by rewrite addrN. Qed.

  Lemma addrNK x y : x + y - y = x.
  Proof. by rewrite -addrA subrr addr0. Qed.

End AddAGTheory.

Elpi hb.declare_mixin Ring_of_AddAG A AddAG.axioms.
  Record axioms := Axioms {
    one : A;
    mul : A -> A -> A;
    mulrA : associative mul;
    mulr1 : left_id one mul;
    mul1r : right_id one mul;
    mulrDl : left_distributive mul add;
    mulrDr : right_distributive mul add;
  }.
Elpi hb.end.
Elpi hb.declare_factory Ring_of_TYPE A.
  Record axioms := Axioms {
    zero : A;
    one : A;
    add : A -> A -> A;
    opp : A -> A;
    mul : A -> A -> A;
    addrA : associative add;
    addrC : commutative add;
    add0r : left_id zero add;
    addNr : left_inverse zero opp add;
    mulrA : associative mul;
    mul1r : left_id one mul;
    mulr1 : right_id one mul;
    mulrDl : left_distributive mul add;
    mulrDr : right_distributive mul add;
  }.

  Variable a : axioms.
  Definition to_AddAG_of_TYPE : AddAG_of_TYPE.axioms_ A :=
    AddAG_of_TYPE.Axioms _ _ _ (addrA a) (addrC a) (add0r a) (addNr a).
  Elpi hb.canonical A to_AddAG_of_TYPE.
  Definition to_Ring_of_AddAG : Ring_of_AddAG.axioms_ A :=
    Ring_of_AddAG.Axioms _ _ (mulrA a) (mul1r a)
      (mulr1 a) (mulrDl a : left_distributive _ (@AddAG.Exports.add _)) (mulrDr a).
Elpi hb.end to_AddAG_of_TYPE to_Ring_of_AddAG.

Elpi hb.structure Ring Ring_of_TYPE.axioms.

Notation "1" := one : hb_scope.
Infix "*" := (@mul _) : hb_scope.

Elpi hb.declare_mixin Topological T.
  Record axioms := Axioms {
    open : (T -> Prop) -> Prop;
    open_setT : open setT;
    open_bigcup : forall {I} (D : set I) (F : I -> set T),
    (forall i, D i -> open (F i)) -> open (\bigcup_(i in D) F i);
    open_setI : forall X Y : set T, open X -> open Y -> open (setI X Y);
    }.
Elpi hb.end.
Elpi hb.structure TopologicalSpace Topological.axioms.

Hint Extern 0 (open setT) => now apply: open_setT : core.

Elpi hb.declare_factory TopologicalBase T.
  Record axioms := Axioms {
    open_base : set (set T);
    open_base_covers : setT `<=` \bigcup_(X in open_base) X;
    open_base_cup : forall X Y : set T, open_base X -> open_base Y ->
      forall z, (X `&` Y) z -> exists2 Z, open_base Z & Z z /\ Z `<=` X `&` Y
  }.
  Variable a : axioms.

  Definition open_of :=
    [set A | exists2 D, D `<=` open_base a & A = \bigcup_(X in D) X].

  Lemma open_of_setT : open_of setT.
  Proof.
  exists (open_base a); rewrite // predeqE => x; split=> // _.
  by apply: open_base_covers.
  Qed.

  Lemma open_of_bigcup {I} (D : set I) (F : I -> set T) :
    (forall i, D i -> open_of (F i)) -> open_of (\bigcup_(i in D) F i).
  Proof. Admitted.

  Lemma open_of_cap X Y : open_of X -> open_of Y -> open_of (X `&` Y).
  Proof. Admitted.

  Definition to_Topological : Topological.axioms_ T :=
    Topological.Axioms _ open_of_setT (@open_of_bigcup) open_of_cap.
  Elpi hb.canonical T to_Topological.

Elpi hb.end to_Topological. (* TODO: infer factories from canonical *)

Section ProductTopology.
  Variables (T1 T2 : TopologicalSpace.type).

  Definition prod_open_base :=
    [set A | exists (A1 : set T1) (A2 : set T2),
      open A1 /\ open A2 /\ A = setM A1 A2].

  Lemma prod_open_base_covers : setT `<=` \bigcup_(X in prod_open_base) X.
  Proof.
  move=> X _; exists setT => //; exists setT, setT; do ?split.
  - exact: open_setT.
  - exact: open_setT.
  - by rewrite predeqE.
  Qed.

  Lemma prod_open_base_setU X Y :
    prod_open_base X -> prod_open_base Y ->
      forall z, (X `&` Y) z ->
        exists2 Z, prod_open_base Z & Z z /\ Z `<=` X `&` Y.
  Proof.
  move=> [A1 [A2 [A1open [A2open ->]]]] [B1 [B2 [B1open [B2open ->]]]].
  move=> [z1 z2] [[/=Az1 Az2] [/= Bz1 Bz2]].
  exists ((A1 `&` B1) `*` (A2 `&` B2)).
    by eexists _, _; do ?[split; last first]; apply: open_setI.
  by split => // [[x1 x2] [[/=Ax1 Bx1] [/=Ax2 Bx2]]].
  Qed.

  Definition prod_topology : TopologicalBase.axioms_ (T1 * T2)%type :=
    TopologicalBase.Axioms _ prod_open_base_covers prod_open_base_setU.

  (* TODO: make elpi insert coercions! *)
  Elpi hb.canonical (TopologicalSpace.sort T1 * TopologicalSpace.sort T2)%type prod_topology.

End ProductTopology.

(* TODO: infer continuous as a morphism of Topology  *)
Definition continuous {T T' : TopologicalSpace.type} (f : T -> T') :=
  forall B : set T', open B -> open (f@^-1` B).

Definition continuous2 {T T' T'': TopologicalSpace.type}
  (f : T -> T' -> T'') := continuous (fun xy => f xy.1 xy.2).

Elpi hb.declare_mixin TAddAG_of_AddAG_Topology_wo_Uniform
  T AddAG_of_TYPE.axioms Topological.axioms.
  Record axioms := Axioms {
    add_continuous : continuous2 (add : T -> T -> T);
    opp_continuous : continuous (opp : T -> T)
  }.
Elpi hb.end.

Elpi hb.structure TAddAG_wo_Uniform
  Topological.axioms AddAG_of_TYPE.axioms
  TAddAG_of_AddAG_Topology_wo_Uniform.axioms.

Elpi hb.declare_mixin Uniform_wo_Topology U.
  Record axioms := Axioms {
    entourage : set (set (U * U)) ;
    filter_entourage : is_filter entourage ;
    entourage_sub : forall A, entourage A -> [set xy | xy.1 = xy.2] `<=` A;
    entourage_sym : forall A, entourage A -> entourage (graph_sym A) ;
    entourage_split : forall A, entourage A ->
      exists2 B, entourage B & graph_comp B B `<=` A ;
  }.
Elpi hb.end.
Elpi hb.structure UniformSpace_wo_Topology Uniform_wo_Topology.axioms.

(* TODO: have a command hb.typealias which register "typealias factories"
   which turn a typealias into factories *)
Definition uniform T : Type := T.

Section Uniform_Topology.
  Variable U : UniformSpace_wo_Topology.type.
  Definition uniform_open : set (set (uniform U)). Admitted.
  Lemma uniform_open_setT : uniform_open setT. Admitted.
  Lemma uniform_open_bigcup : forall {I} (D : set I) (F : I -> set U),
    (forall i, D i -> uniform_open (F i)) -> uniform_open (\bigcup_(i in D) F i).
  Admitted.
  Lemma uniform_open_setI : forall X Y : set U,
     uniform_open X -> uniform_open Y -> uniform_open (setI X Y).
  Admitted.

  Definition uniform_topology : Topological.axioms_ U :=
    Topological.Axioms _ uniform_open_setT (@uniform_open_bigcup) uniform_open_setI.
  Elpi hb.canonical (uniform (UniformSpace_wo_Topology.sort U)) uniform_topology.

End Uniform_Topology.

Elpi hb.declare_mixin Join_Uniform_Topology U
    Topological.axioms Uniform_wo_Topology.axioms.

  Record axioms := Axioms {
    openE : open = (uniform_open _ : set (set (uniform U)))
  }.
Elpi hb.end.

(* TODO: this factory should be replaced by type alias uniform *)
Elpi hb.declare_factory Uniform_Topology U Uniform_wo_Topology.axioms.
  Definition axioms := let _ := Uniform_wo_Topology.axioms_ U in True. (* fix bug *)
  Definition Axioms : axioms := I.

  Definition to_Topological : Topological.axioms_ U := (uniform_topology _).
Elpi hb.end to_Topological.

Elpi hb.structure UniformSpace
   Uniform_Topology.axioms     (* should be replaced by typealias uniform *)
   Uniform_wo_Topology.axioms. (* TODO: should be ommited                 *)

(* TODO: this is another typealias *)
Definition TAddAG (T : Type) := T.

Section TAddAGUniform.
  Variable T : TAddAG_wo_Uniform.type.
  Notation TT := (TAddAG T).
  Definition TAddAG_entourage : set (set (TT * TT)).
  Admitted.
  Lemma filter_TAddAG_entourage : is_filter TAddAG_entourage.
  Admitted.
  Lemma TAddAG_entourage_sub : forall A, TAddAG_entourage A -> [set xy | xy.1 = xy.2] `<=` A.
  Admitted.
  Lemma TAddAG_entourage_sym : forall A, TAddAG_entourage A -> TAddAG_entourage (graph_sym A).
  Admitted.
  Lemma TAddAG_entourage_split : forall A, TAddAG_entourage A ->
      exists2 B, TAddAG_entourage B & graph_comp B B `<=` A.
  Admitted.

  Definition TAddAG_uniform : Uniform_wo_Topology.axioms_ TT :=
    Uniform_wo_Topology.Axioms _ filter_TAddAG_entourage TAddAG_entourage_sub
      TAddAG_entourage_sym TAddAG_entourage_split.
  Elpi hb.canonical (TAddAG (TAddAG_wo_Uniform.sort T)) TAddAG_uniform.

  Lemma TAddAG_uniform_topologyE :
     open = (uniform_open _ : set (set (uniform TT))).
  Admitted.
  Definition TAddAG_Join_Uniform_Topology : Join_Uniform_Topology.axioms_ (TAddAG T)
    := Join_Uniform_Topology.Axioms TAddAG_uniform_topologyE.
  Elpi hb.canonical (TAddAG (TAddAG_wo_Uniform.sort T))
    TAddAG_Join_Uniform_Topology.

  Lemma TAddAG_entourageE :
    entourage = (TAddAG_entourage : set (set (TAddAG T * TAddAG T))).
  Admitted.

End TAddAGUniform.

Elpi hb.structure Uniform_TAddAG_unjoined
  TAddAG_wo_Uniform.axioms Uniform_wo_Topology.axioms.
  (* should be created automatically *)

Elpi hb.declare_mixin Join_TAddAG_Uniform T
     Uniform_TAddAG_unjoined.axioms.
  Record axioms := Axioms {
      entourageE :
      entourage = (TAddAG_entourage _ : set (set (TAddAG T * TAddAG T)))
  }.
Elpi hb.end.
Print Join_TAddAG_Uniform.phant_axioms_.

(* TODO: should be subsumed by the type alias TAddAG *)
Elpi hb.declare_factory TAddAG_Uniform U TAddAG_wo_Uniform.axioms.
  Definition axioms :=
    let _ := Topological.axioms_ U in
    let _ :=  AddAG_of_TYPE.axioms_ U in
    let _ := TAddAG_of_AddAG_Topology_wo_Uniform.axioms_ U in
    True. (* fix bug *)
  Definition Axioms : axioms := I.

  Definition to_Uniform_wo_Topology : Uniform_wo_Topology.axioms_ U := (TAddAG_uniform _).
  Elpi hb.canonical U to_Uniform_wo_Topology.
  Definition to_Join_Uniform_Topology : Join_Uniform_Topology.axioms_ U :=
    (TAddAG_Join_Uniform_Topology _).
  Elpi hb.canonical U to_Join_Uniform_Topology.
  Definition to_Join_TAddAG_Uniform : Join_TAddAG_Uniform.axioms_ U :=
    (Join_TAddAG_Uniform.Axioms (TAddAG_entourageE _)).
  Elpi hb.canonical U to_Join_TAddAG_Uniform.

Elpi hb.end to_Uniform_wo_Topology to_Join_Uniform_Topology
  to_Join_TAddAG_Uniform.

Elpi hb.structure TAddAG
   TAddAG_Uniform.axioms (* TODO: should be replaced by type alias TAddAG *)
   TAddAG_wo_Uniform.axioms (* TODO: should be omitted *)
   TAddAG_of_AddAG_Topology_wo_Uniform.axioms. (* TODO: should be omitted *)

(* Instance *)

Definition Z_ring_axioms : Ring_of_TYPE.axioms_ Z :=
  Ring_of_TYPE.Axioms 0%Z 1%Z Z.add Z.opp Z.mul
    Z.add_assoc Z.add_comm Z.add_0_l Z.add_opp_diag_l
    Z.mul_assoc Z.mul_1_l Z.mul_1_r
    Z.mul_add_distr_r Z.mul_add_distr_l.
Elpi hb.canonical Z Z_ring_axioms.

Example test1 (m n : Z) : (m + n) - n + 0 = m.
Proof. by rewrite addrNK addr0. Qed.

End Stage11.