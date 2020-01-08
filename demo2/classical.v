Require Import ssreflect ssrfun ssrbool ssrfun ssrbool.
(******************************************************************************)
(* This file develops a basic theory of sets under classical axiomatization   *)
(* and is imported from math-comp/analysis                                    *)
(*                                                                            *)
(* --> A decidable equality is defined for any type. It is thus possible to   *)
(*     define an eqType structure for any type using the mixin gen_eqMixin.   *)
(* --> This file adds the possibility to define a choiceType structure for    *)
(*     any type thanks to an axiom gen_choiceMixin giving a choice mixin.     *)
(* --> We chose to have generic mixins and no global instances of the eqType  *)
(*     and choiceType structures to let the user choose which definition of   *)
(*     equality to use and to avoid conflict with already declared instances. *)
(*                                                                            *)
(* * Sets:                                                                    *)
(*                       set A == type of sets on A.                          *)
(*                   (x \in P) == boolean membership predicate from ssrbool   *)
(*                                for set P, available thanks to a canonical  *)
(*                                predType T structure on sets on T.          *)
(*             [set x : T | P] == set of points x : T such that P holds.      *)
(*                 [set x | P] == same as before with T left implicit.        *)
(*            [set E | x in A] == set defined by the expression E for x in    *)
(*                                set A.                                      *)
(*   [set E | x in A & y in B] == same as before for E depending on 2         *)
(*                                variables x and y in sets A and B.          *)
(*                        setT == full set.                                   *)
(*                        set0 == empty set.                                  *)
(*                  [set of F] == set defined by the expression F x for any   *)
(*                                x.                                          *)
(*                     [set a] == set containing only a.                      *)
(*                 [set a : T] == same as before with the type of a made      *)
(*                                explicit.                                   *)
(*                     A `|` B == union of A and B.                           *)
(*                      a |` A == A extended with a.                          *)
(*        [set a1; a2; ..; an] == set containing only the n elements ai.      *)
(*                     A `&` B == intersection of A and B.                    *)
(*                     A `*` B == product of A and B, i.e. set of pairs (a,b) *)
(*                                such that A a and B b.                      *)
(*                        A.`1 == set of points a such that there exists b so *)
(*                                that A (a, b).                              *)
(*                        A.`2 == set of points a such that there exists b so *)
(*                                that A (b, a).                              *)
(*                        ~` A == complement of A.                            *)
(*                   [set ~ a] == complement of [set a].                      *)
(*                     A `\` B == complement of B in A.                       *)
(*                      A `\ a == A deprived of a.                            *)
(*          \bigcup_(i in P) F == union of the elements of the family F whose *)
(*                                index satisfies P.                          *)
(*           \bigcup_(i : T) F == union of the family F indexed on T.         *)
(*                 \bigcup_i F == same as before with T left implicit.        *)
(*          \bigcap_(i in P) F == intersection of the elements of the family  *)
(*                                F whose index satisfies P.                  *)
(*           \bigcap_(i : T) F == union of the family F indexed on T.         *)
(*                 \bigcap_i F == same as before with T left implicit.        *)
(*                   A `<=` B <-> A is included in B.                         *)
(*                  A `<=>` B <-> double inclusion A `<=` B and B `<=` A.     *)
(*                   f @^-1` A == preimage of A by f.                         *)
(*                      f @` A == image of A by f.                            *)
(*                    A !=set0 := exists x, A x.                              *)
(*             is_singleton X <-> X contains only 1 element.                  *)
(*                   is_fun f <-> for each a, f a contains only 1 element.    *)
(*                 is_total f <-> for each a, f a is non empty.               *)
(*              is_totalfun f <-> conjunction of is_fun and is_total.         *)
(*                   xget x0 P == point x in P if it exists, x0 otherwise;    *)
(*                                P must be a set on a choiceType.            *)
(*             fun_of_graph f0 f == function that maps x to an element of f x   *)
(*                                if there is one, to f0 x otherwise.         *)
(*                                                                            *)
(* --> Thanks to this basic set theory, we proved Zorn's Lemma, which states  *)
(*     that any ordered set such that every totally ordered subset admits an  *)
(*     upper bound has a maximal element. We also proved an analogous version *)
(*     for preorders, where maximal is replaced with premaximal: t is         *)
(*     premaximal if whenever t < s we also have s < t.                       *)
(******************************************************************************)


(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope box_scope.
Declare Scope quant_scope.

(* Copy of the ssrbool shim to ensure compatibility with MathComp v1.8.0. *)
Definition PredType : forall T pT, (pT -> pred T) -> predType T.
exact PredType || exact mkPredType.
Defined.
Arguments PredType [T pT] toP.

Local Notation predOfType T := (pred_of_simpl (@pred_of_argType T)).

(* -------------------------------------------------------------------- *)

Axiom functional_extensionality_dep :
       forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
       (forall x : A, f x = g x) -> f = g.
Axiom propositional_extensionality :
       forall P Q : Prop, P <-> Q -> P = Q.

Axiom constructive_indefinite_description :
  forall (A : Type) (P : A -> Prop),
  (exists x : A, P x) -> {x : A | P x}.
Notation cid := constructive_indefinite_description.

(* -------------------------------------------------------------------- *)
Record mextentionality := {
  _ : forall (P Q : Prop), (P <-> Q) -> (P = Q);
  _ : forall {T U : Type} (f g : T -> U),
        (forall x, f x = g x) -> f = g;
}.

Fact extentionality : mextentionality.
Proof.
split.
- exact: propositional_extensionality.
- by move=> T U f g; apply: functional_extensionality_dep.
Qed.

Lemma propext (P Q : Prop) : (P <-> Q) -> (P = Q).
Proof. by have [propext _] := extentionality; apply: propext. Qed.

Lemma funext {T U : Type} (f g : T -> U) : (f =1 g) -> f = g.
Proof. by case: extentionality=> _; apply. Qed.

Lemma propeqE (P Q : Prop) : (P = Q) = (P <-> Q).
Proof. by apply: propext; split=> [->|/propext]. Qed.


Lemma funeqE {T U : Type} (f g : T -> U) : (f = g) = (f =1 g).
Proof. by rewrite propeqE; split=> [->//|/funext]. Qed.

Lemma funeq2E {T U V : Type} (f g : T -> U -> V) : (f = g) = (f =2 g).
Proof.
by rewrite propeqE; split=> [->//|?]; rewrite funeqE=> x; rewrite funeqE.
Qed.

Lemma funeq3E {T U V W : Type} (f g : T -> U -> V -> W) :
  (f = g) = (forall x y z, f x y z = g x y z).
Proof.
by rewrite propeqE; split=> [->//|?]; rewrite funeq2E=> x y; rewrite funeqE.
Qed.

Lemma predeqE {T} (P Q : T -> Prop) : (P = Q) = (forall x, P x <-> Q x).
Proof.
by rewrite propeqE; split=> [->//|?]; rewrite funeqE=> x; rewrite propeqE.
Qed.

Lemma predeq2E {T U} (P Q : T -> U -> Prop) :
   (P = Q) = (forall x y, P x y <-> Q x y).
Proof.
by rewrite propeqE; split=> [->//|?]; rewrite funeq2E=> ??; rewrite propeqE.
Qed.

Lemma predeq3E {T U V} (P Q : T -> U -> V -> Prop) :
   (P = Q) = (forall x y z, P x y z <-> Q x y z).
Proof.
by rewrite propeqE; split=> [->//|?]; rewrite funeq3E=> ???; rewrite propeqE.
Qed.

Lemma propT (P : Prop) : P -> P = True.
Proof. by move=> p; rewrite propeqE; tauto. Qed.

Lemma Prop_irrelevance (P : Prop) (x y : P) : x = y.
Proof. by move: x (x) y => /propT-> [] []. Qed.

Lemma choice X Y (P : X -> Y -> Prop) :
  (forall x, exists y, P x y) -> {f & forall x, P x (f x)}.
Proof. by move=> /(_ _)/constructive_indefinite_description -/all_tag. Qed.

(* Diaconescu Theorem *)
Theorem EM P : P \/ ~ P.
Proof.
pose U val := fun Q : bool => Q = val \/ P.
have Uex val : exists b, U val b by exists val; left.
pose f val := projT1 (cid (Uex val)).
pose Uf val : U val (f val) := projT2 (cid (Uex val)).
have : f true <> f false \/ P.
  have [] := (Uf true, Uf false); rewrite /U.
  by move=> [->|?] [->|?] ; do ?[by right]; left.
move=> [fTFN|]; [right=> p|by left]; apply: fTFN.
have UTF : U true = U false by rewrite predeqE /U => b; split=> _; right.
rewrite /f; move: (Uex true) (Uex false); rewrite UTF => p1 p2.
by congr (projT1 (cid _)); apply: Prop_irrelevance.
Qed.

Lemma pselect (P : Prop): {P} + {~P}.
Proof.
have : exists b, if b then P else ~ P.
  by case: (EM P); [exists true|exists false].
by move=> /cid [[]]; [left|right].
Qed.

Lemma pdegen (P : Prop): P = True \/ P = False.
Proof. by have [p|Np] := pselect P; [left|right]; rewrite propeqE. Qed.

Lemma lem (P : Prop): P \/ ~P.
Proof. by case: (pselect P); tauto. Qed.

(* -------------------------------------------------------------------- *)
Lemma trueE : true = True :> Prop.
Proof. by rewrite propeqE; split. Qed.

Lemma falseE : false = False :> Prop.
Proof. by rewrite propeqE; split. Qed.

Lemma propF (P : Prop) : ~ P -> P = False.
Proof. by move=> p; rewrite propeqE; tauto. Qed.

Lemma eq_forall T (U V : T -> Prop) :
  (forall x : T, U x = V x) -> (forall x, U x) = (forall x, V x).
Proof. by move=> e; rewrite propeqE; split=> ??; rewrite (e,=^~e). Qed.

Lemma eq_exists T (U V : T -> Prop) :
  (forall x : T, U x = V x) -> (exists x, U x) = (exists x, V x).
Proof.
by move=> e; rewrite propeqE; split=> - [] x ?; exists x; rewrite (e,=^~e).
Qed.

Lemma reflect_eq (P : Prop) (b : bool) : reflect P b -> P = b.
Proof. by rewrite propeqE; exact: rwP. Qed.

Definition asbool (P : Prop) :=
  if pselect P then true else false.

Notation "`[< P >]" := (asbool P) : bool_scope.

Lemma asboolE (P : Prop) : `[<P>] = P :> Prop.
Proof. by rewrite propeqE /asbool; case: pselect; split. Qed.

Lemma asboolP (P : Prop) : reflect P `[<P>].
Proof. by apply: (equivP idP); rewrite asboolE. Qed.

Lemma asboolPn (P : Prop) : reflect (~ P) (~~ `[<P>]).
Proof. by rewrite /asbool; case: pselect=> h; constructor. Qed.

Lemma asboolW (P : Prop) : `[<P>] -> P.
Proof. by case: asboolP. Qed.

(* Shall this be a coercion ?*)
Lemma asboolT (P : Prop) : P -> `[<P>].
Proof. by case: asboolP. Qed.

Lemma asboolF (P : Prop) : ~ P -> `[<P>] = false.
Proof. by apply/introF/asboolP. Qed.

Lemma is_true_inj : injective is_true.
Proof. by move=> [] []; rewrite ?(trueE, falseE) ?propeqE; tauto. Qed.

(* -------------------------------------------------------------------- *)
Lemma asbool_equiv_eq {P Q : Prop} : (P <-> Q) -> `[<P>] = `[<Q>].
Proof. by rewrite -propeqE => ->. Qed.

Lemma asbool_equiv_eqP {P Q : Prop} QQ : reflect Q QQ -> (P <-> Q) -> `[<P>] = QQ.
Proof.
move=> Q_QQ [hPQ hQP]; apply/idP/Q_QQ=> [/asboolP//|].
by move=> hQ; apply/asboolP/hQP.
Qed.

Lemma asbool_equiv {P Q : Prop} : (P <-> Q) -> (`[<P>] <-> `[<Q>]).
Proof. by move/asbool_equiv_eq->. Qed.

Lemma asbool_eq_equiv {P Q : Prop} : `[<P>] = `[<Q>] -> (P <-> Q).
Proof.
by move=> eq; split=> /asboolP; rewrite (eq, =^~ eq) => /asboolP.
Qed.

(* -------------------------------------------------------------------- *)
Lemma and_asboolP (P Q : Prop) : reflect (P /\ Q) (`[<P>] && `[<Q>]).
Proof.
apply: (iffP idP); first by case/andP=> /asboolP hP /asboolP hQ.
by case=> /asboolP-> /asboolP->.
Qed.

Lemma or_asboolP (P Q : Prop) : reflect (P \/ Q) (`[<P>] || `[<Q>]).
Proof.
apply: (iffP idP); first by case/orP=> /asboolP; [left | right].
by case=> /asboolP-> //=; rewrite orbT.
Qed.

Lemma asbool_neg {P : Prop} : `[<~ P>] = ~~ `[<P>].
Proof. by apply/idP/asboolPn=> [/asboolP|/asboolT]. Qed.

Lemma asbool_or {P Q : Prop} : `[<P \/ Q>] = `[<P>] || `[<Q>].
Proof. exact: (asbool_equiv_eqP (or_asboolP _ _)). Qed.

Lemma asbool_and {P Q : Prop} : `[<P /\ Q>] = `[<P>] && `[<Q>].
Proof. exact: (asbool_equiv_eqP (and_asboolP _ _)). Qed.

(* -------------------------------------------------------------------- *)
Lemma imply_asboolP {P Q : Prop} : reflect (P -> Q) (`[<P>] ==> `[<Q>]).
Proof.
apply: (iffP implyP)=> [PQb /asboolP/PQb/asboolW //|].
by move=> PQ /asboolP/PQ/asboolT.
Qed.

Lemma asbool_imply {P Q : Prop} : `[<P -> Q>] = `[<P>] ==> `[<Q>].
Proof. exact: (asbool_equiv_eqP imply_asboolP). Qed.

Lemma imply_asboolPn (P Q : Prop) : reflect (P /\ ~ Q) (~~ `[<P -> Q>]).
Proof.
apply: (iffP idP).
by rewrite asbool_imply negb_imply -asbool_neg => /and_asboolP.
by move/and_asboolP; rewrite asbool_neg -negb_imply asbool_imply.
Qed.

(* -------------------------------------------------------------------- *)
Lemma forall_asboolP {T : Type} (P : T -> Prop) :
  reflect (forall x, `[<P x>]) (`[<forall x, P x>]).
Proof.
apply: (iffP idP); first by move/asboolP=> Px x; apply/asboolP.
by move=> Px; apply/asboolP=> x; apply/asboolP.
Qed.

Lemma exists_asboolP {T : Type} (P : T -> Prop) :
  reflect (exists x, `[<P x>]) (`[<exists x, P x>]).
Proof.
apply: (iffP idP); first by case/asboolP=> x Px; exists x; apply/asboolP.
by case=> x bPx; apply/asboolP; exists x; apply/asboolP.
Qed.

(* -------------------------------------------------------------------- *)
Lemma contrap (Q P : Prop) : (Q -> P) -> ~ P -> ~ Q.
Proof.
move=> cb /asboolPn nb; apply/asboolPn.
by apply: contra nb => /asboolP /cb /asboolP.
Qed.

Definition contrapNN := contra.

Lemma contrapL (Q P : Prop) : (Q -> ~ P) -> P -> ~ Q.
Proof.
move=> cb /asboolP hb; apply/asboolPn.
by apply: contraL hb => /asboolP /cb /asboolPn.
Qed.

Definition contrapTN := contrapL.

Lemma contrapR (Q P : Prop) : (~ Q -> P) -> ~ P -> Q.
Proof.
move=> cb /asboolPn nb; apply/asboolP.
by apply: contraR nb => /asboolP /cb /asboolP.
Qed.

Definition contrapNT := contrapR.

Lemma contrapLR (Q P : Prop) : (~ Q -> ~ P) -> P -> Q.
Proof.
move=> cb /asboolP hb; apply/asboolP.
by apply: contraLR hb => /asboolP /cb /asboolPn.
Qed.

Definition contrapTT := contrapLR.

Lemma contrapT P : ~ ~ P -> P.
Proof.
by move/asboolPn=> nnb; apply/asboolP; apply: contraR nnb => /asboolPn /asboolP.
Qed.

Lemma wlog_neg P : (~ P -> P) -> P.
Proof. by move=> ?; case: (pselect P). Qed.

Lemma notT (P : Prop) : P = False -> ~ P. Proof. by move->. Qed.

Lemma notTE (P : Prop) : (~ P) -> P = False. Proof. by case: (pdegen P)=> ->. Qed.
Lemma notFE (P : Prop) : (~ P) = False -> P.
Proof. move/notT; exact: contrapT. Qed.

Lemma notK : involutive not.
Proof.
move=> P; case: (pdegen P)=> ->; last by apply: notTE; intuition.
by rewrite [~ True]notTE //; case: (pdegen (~ False)) => // /notFE.
Qed.

Lemma not_inj : injective not. Proof. exact: can_inj notK. Qed.
Lemma notLR P Q : (P = ~ Q) -> (~ P) = Q. Proof. exact: canLR notK. Qed.

Lemma notRL P Q : (~ P) = Q -> P = ~ Q. Proof. exact: canRL notK. Qed.

(* -------------------------------------------------------------------- *)
(* assia : let's see if we need the simplpred machinery. In any case, we sould
   first try definitions + appropriate Arguments setting to see whether these
   can replace the canonical structures machinery. *)

Definition predp T := T -> Prop.

Identity Coercion fun_of_pred : predp >-> Funclass.

Definition relp T := T -> predp T.

Identity Coercion fun_of_rel : rel >-> Funclass.

Notation xpredp0 := (fun _ => False).
Notation xpredpT := (fun _ => True).
Notation xpredpI := (fun (p1 p2 : predp _) x => p1 x /\ p2 x).
Notation xpredpU := (fun (p1 p2 : predp _) x => p1 x \/ p2 x).
Notation xpredpC := (fun (p : predp _) x => ~ p x).
Notation xpredpD := (fun (p1 p2 : predp _) x => ~ p2 x /\ p1 x).
Notation xpreimp := (fun f (p : predp _) x => p (f x)).
Notation xrelpU := (fun (r1 r2 : relp _) x y => r1 x y \/ r2 x y).

(* -------------------------------------------------------------------- *)
Definition pred0p (T : Type) (P : predp T) : bool := `[<P =1 xpredp0>].
Prenex Implicits pred0p.

Lemma pred0pP  (T : Type) (P : predp T) : reflect (P =1 xpredp0) (pred0p P).
Proof. by apply: (iffP (asboolP _)). Qed.

(* -------------------------------------------------------------------- *)
Module BoolQuant.

Inductive box := Box of bool.

Bind    Scope box_scope with box.
Delimit Scope box_scope with P.

Definition idbox {T : Type} (B : box) := fun (x : T) => B.

Definition unbox {T : Type} (B : T -> box) : bool :=
  asbool (forall x : T, let: Box b := B x in b).

Notation "F ^*" := (Box F) (at level 2).
Notation "F ^~" := (~~ F) (at level 2).

Section Definitions.

Variable T : Type.
Implicit Types (B : box) (x y : T).

Definition quant0p Bp := pred0p (fun x : T => let: F^* := Bp x x in F).
(* The first redundant argument protects the notation from  Coq's K-term      *)
(* display kludge; the second protects it from simpl and /=.                  *)
Definition ex B x y := B.
(* Binding the predicate value rather than projecting it prevents spurious    *)
(* unfolding of the boolean connectives by unification.                       *)
Definition all B x y := let: F^* := B in F^~^*.
Definition all_in C B x y := let: F^* := B in (C ==> F)^~^*.
Definition ex_in C B x y :=  let: F^* := B in (C && F)^*.

End Definitions.


Notation "`[ x | B ]" := (quant0p (fun x => B x)) (at level 0, x ident).
Notation "`[ x : T | B ]" := (quant0p (fun x : T => B x)) (at level 0, x ident).

Module Exports.

Delimit Scope quant_scope with Q. (* Bogus, only used to declare scope. *)
Bind Scope quant_scope with box.

Notation ", F" := F^* (at level 200, format ", '/ '  F") : quant_scope.

Notation "`[ 'forall' x B ]" := `[x | all B]
  (at level 0, x at level 99, B at level 200,
   format "`[ '[hv' 'forall'  x B ] ']'") : bool_scope.

Notation "`[ 'forall' x : T B ]" := `[x : T | all B]
  (at level 0, x at level 99, B at level 200, only parsing) : bool_scope.
Notation "`[ 'forall' ( x | C ) B ]" := `[x | all_in C B]
  (at level 0, x at level 99, B at level 200,
   format "`[ '[hv' '[' 'forall'  ( x '/  '  |  C ) ']' B ] ']'") : bool_scope.
Notation "`[ 'forall' ( x : T | C ) B ]" := `[x : T | all_in C B]
  (at level 0, x at level 99, B at level 200, only parsing) : bool_scope.
Notation "`[ 'forall' x 'in' A B ]" := `[x | all_in (x \in A) B]
  (at level 0, x at level 99, B at level 200,
   format "`[ '[hv' '[' 'forall'  x '/  '  'in'  A ']' B ] ']'") : bool_scope.
Notation "`[ 'forall' x : T 'in' A B ]" := `[x : T | all_in (x \in A) B]
  (at level 0, x at level 99, B at level 200, only parsing) : bool_scope.
Notation ", 'forall' x B" := `[x | all B]^*
  (at level 200, x at level 99, B at level 200,
   format ", '/ '  'forall'  x B") : quant_scope.
Notation ", 'forall' x : T B" := `[x : T | all B]^*
  (at level 200, x at level 99, B at level 200, only parsing) : quant_scope.
Notation ", 'forall' ( x | C ) B" := `[x | all_in C B]^*
  (at level 200, x at level 99, B at level 200,
   format ", '/ '  '[' 'forall'  ( x '/  '  |  C ) ']' B") : quant_scope.
Notation ", 'forall' ( x : T | C ) B" := `[x : T | all_in C B]^*
  (at level 200, x at level 99, B at level 200, only parsing) : quant_scope.
Notation ", 'forall' x 'in' A B" := `[x | all_in (x \in A) B]^*
  (at level 200, x at level 99, B at level 200,
   format ", '/ '  '[' 'forall'  x '/  '  'in'  A ']' B") : bool_scope.
Notation ", 'forall' x : T 'in' A B" := `[x : T | all_in (x \in A) B]^*
  (at level 200, x at level 99, B at level 200, only parsing) : bool_scope.

Notation "`[ 'exists' x B ]" := `[x | ex B]^~
  (at level 0, x at level 99, B at level 200,
   format "`[ '[hv' 'exists'  x B ] ']'") : bool_scope.
Notation "`[ 'exists' x : T B ]" := `[x : T | ex B]^~
  (at level 0, x at level 99, B at level 200, only parsing) : bool_scope.
Notation "`[ 'exists' ( x | C ) B ]" := `[x | ex_in C B]^~
  (at level 0, x at level 99, B at level 200,
   format "`[ '[hv' '[' 'exists'  ( x '/  '  |  C ) ']' B ] ']'") : bool_scope.
Notation "`[ 'exists' ( x : T | C ) B ]" := `[x : T | ex_in C B]^~
  (at level 0, x at level 99, B at level 200, only parsing) : bool_scope.
Notation "`[ 'exists' x 'in' A B ]" := `[x | ex_in (x \in A) B]^~
  (at level 0, x at level 99, B at level 200,
   format "`[ '[hv' '[' 'exists'  x '/  '  'in'  A ']' B ] ']'") : bool_scope.
Notation "`[ 'exists' x : T 'in' A B ]" := `[x : T | ex_in (x \in A) B]^~
  (at level 0, x at level 99, B at level 200, only parsing) : bool_scope.
Notation ", 'exists' x B" := `[x | ex B]^~^*
  (at level 200, x at level 99, B at level 200,
   format ", '/ '  'exists'  x B") : quant_scope.
Notation ", 'exists' x : T B" := `[x : T | ex B]^~^*
  (at level 200, x at level 99, B at level 200, only parsing) : quant_scope.
Notation ", 'exists' ( x | C ) B" := `[x | ex_in C B]^~^*
  (at level 200, x at level 99, B at level 200,
   format ", '/ '  '[' 'exists'  ( x '/  '  |  C ) ']' B") : quant_scope.
Notation ", 'exists' ( x : T | C ) B" := `[x : T | ex_in C B]^~^*
  (at level 200, x at level 99, B at level 200, only parsing) : quant_scope.
Notation ", 'exists' x 'in' A B" := `[x | ex_in (x \in A) B]^~^*
  (at level 200, x at level 99, B at level 200,
   format ", '/ '  '[' 'exists'  x '/  '  'in'  A ']' B") : bool_scope.
Notation ", 'exists' x : T 'in' A B" := `[x : T | ex_in (x \in A) B]^~^*
  (at level 200, x at level 99, B at level 200, only parsing) : bool_scope.

End Exports.

End BoolQuant.
Export BoolQuant.Exports.

Open Scope quant_scope.

(* -------------------------------------------------------------------- *)
Section QuantifierCombinators.

Variables (T : Type) (P : pred T) (PP : predp T).
Hypothesis viewP : forall x, reflect (PP x) (P x).

Lemma existsPP : reflect (exists x, PP x) `[exists x, P x].
Proof.
apply: (iffP idP).
  move/asboolP; (* oops notation! *) apply: contrapR => nh x /=; apply: notTE.
  by apply: contrap nh => /viewP Px; exists x.
case=> x PPx; apply/asboolP=> /(_ x) /notT /=; rewrite -/(not (~ P x)) notK.
exact/viewP.
Qed.

Lemma forallPP : reflect (forall x, PP x) `[forall x, P x].
Proof.
apply: (iffP idP).
  by move/asboolP=> h x; move/notT: (h x)=> /= /negP; rewrite negbK => /viewP.
move=> h; apply/asboolP=> x; apply/notTE/negP; rewrite negbK; exact/viewP.
Qed.

End QuantifierCombinators.

Section PredQuantifierCombinators.

Variables (T : Type) (P : pred T).

Lemma existsbP : reflect (exists x, P x) `[exists x, P x].
Proof. exact: existsPP (fun x => @idP (P x)). Qed.

Lemma existsbE : `[exists x, P x] = `[<exists x, P x>].
Proof.
apply/esym/is_true_inj; rewrite asboolE propeqE; apply: rwP; exact: existsbP.
Qed.

Lemma forallbP : reflect (forall x, P x) `[forall x, P x].
Proof. exact: forallPP (fun x => @idP (P x)). Qed.

Lemma forallbE : `[forall x, P x] = `[<forall x, P x>].
Proof.
apply/esym/is_true_inj; rewrite asboolE propeqE; apply: rwP; exact: forallbP.
Qed.

End PredQuantifierCombinators.

(* -------------------------------------------------------------------- *)
Lemma existsp_asboolP {T} {P : T -> Prop} :
  reflect (exists x : T, P x) `[exists x : T, `[<P x>]].
Proof. exact: existsPP (fun x => @asboolP (P x)). Qed.

Lemma forallp_asboolP {T} {P : T -> Prop} :
  reflect (forall x : T, P x) `[forall x : T, `[<P x>]].
Proof. exact: forallPP (fun x => @asboolP (P x)). Qed.

Lemma forallp_asboolPn {T} {P : T -> Prop} :
  reflect (forall x : T, ~ P x) (~~ `[<exists x : T, P x>]).
Proof.
apply: (iffP idP)=> [/asboolPn NP x Px|NP].
by apply/NP; exists x. by apply/asboolP=> -[x]; apply/NP.
Qed.

Lemma existsp_asboolPn {T} {P : T -> Prop} :
  reflect (exists x : T, ~ P x) (~~ `[<forall x : T, P x>]).
Proof.
apply: (iffP idP); last by case=> x NPx; apply/asboolPn=> /(_ x).
move/asboolPn=> NP; apply/asboolP/negbNE/asboolPn=> h.
by apply/NP=> x; apply/asboolP/negbNE/asboolPn=> NPx; apply/h; exists x.
Qed.

Lemma asbool_forallNb {T : Type} (P : pred T) :
  `[< forall x : T, ~~ (P x) >] = ~~ `[< exists x : T, P x >].
Proof.
apply: (asbool_equiv_eqP forallp_asboolPn);
  by split=> h x; apply/negP/h.
Qed.

Lemma asbool_existsNb {T : Type} (P : pred T) :
  `[< exists x : T, ~~ (P x) >] = ~~ `[< forall x : T, P x >].
Proof.
apply: (asbool_equiv_eqP existsp_asboolPn);
  by split=> -[x h]; exists x; apply/negP.
Qed.
Reserved Notation "[ 'set' x : T | P ]"
  (at level 0, x at level 99, only parsing).
Reserved Notation "[ 'set' x | P ]"
  (at level 0, x, P at level 99, format "[ 'set'  x  |  P ]").
Reserved Notation "[ 'set' E | x 'in' A ]" (at level 0, E, x at level 99,
  format "[ '[hv' 'set'  E '/ '  |  x  'in'  A ] ']'").
Reserved Notation "[ 'set' E | x 'in' A & y 'in' B ]"
  (at level 0, E, x at level 99,
  format "[ '[hv' 'set'  E '/ '  |  x  'in'  A  &  y  'in'  B ] ']'").
Reserved Notation "[ 'set' 'of' F ]" (at level 0, format "[ 'set'  'of'  F ]").
Reserved Notation "[ 'set' a ]"
  (at level 0, a at level 99, format "[ 'set'  a ]").
Reserved Notation "[ 'set' a : T ]"
  (at level 0, a at level 99, format "[ 'set'  a   :  T ]").
Reserved Notation "A `|` B" (at level 52, left associativity).
Reserved Notation "a |` A" (at level 52, left associativity).
Reserved Notation "[ 'set' a1 ; a2 ; .. ; an ]"
  (at level 0, a1 at level 99, format "[ 'set'  a1 ;  a2 ;  .. ;  an ]").
Reserved Notation "A `&` B"  (at level 48, left associativity).
Reserved Notation "A `*` B"  (at level 46, left associativity).
Reserved Notation "A .`1" (at level 2, left associativity, format "A .`1").
Reserved Notation "A .`2" (at level 2, left associativity, format "A .`2").
Reserved Notation "~` A" (at level 35, right associativity).
Reserved Notation "[ 'set' ~ a ]" (at level 0, format "[ 'set' ~  a ]").
Reserved Notation "A `\` B" (at level 50, left associativity).
Reserved Notation "A `\ b" (at level 50, left associativity).
(*
Reserved Notation "A `+` B"  (at level 54, left associativity).
Reserved Notation "A +` B"  (at level 54, left associativity).
*)
Reserved Notation "\bigcup_ ( i 'in' P ) F"
  (at level 41, F at level 41, i, P at level 50,
           format "'[' \bigcup_ ( i  'in'  P ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i : T ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcup_ ( i  :  T ) '/  '  F ']'").
Reserved Notation "\bigcup_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \bigcup_ i '/  '  F ']'").
Reserved Notation "\bigcap_ ( i 'in' P ) F"
  (at level 41, F at level 41, i, P at level 50,
           format "'[' \bigcap_ ( i  'in'  P ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i : T ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcap_ ( i  :  T ) '/  '  F ']'").
Reserved Notation "\bigcap_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \bigcap_ i '/  '  F ']'").
Reserved Notation "A `<=` B" (at level 70, no associativity).
Reserved Notation "A `<=>` B" (at level 70, no associativity).
Reserved Notation "f @^-1` A" (at level 24).
Reserved Notation "f @` A" (at level 24).
Reserved Notation "A !=set0" (at level 80).

Definition set A := A -> Prop.
Definition in_set T (P : set T) : pred T := [pred x | `[<P x>]].
Canonical set_predType T := @PredType T (set T) (@in_set T).

Lemma in_setE T (P : set T) x : x \in P = P x :> Prop.
Proof. by rewrite propeqE; split => [] /asboolP. Qed.

Declare Scope classical_set_scope.
Bind Scope classical_set_scope with set.
Local Open Scope classical_set_scope.
Delimit Scope classical_set_scope with classic.

Definition mkset {T} (A : T -> Prop) : set T := A.
Notation "[ 'set' x : T | P ]" := (mkset (fun x : T => P)) : classical_set_scope.
Notation "[ 'set' x | P ]" := [set x : _ | P] : classical_set_scope.
Notation "[ 'set' E | x 'in' A ]" :=
  [set y | exists2 x, A x & E = y] : classical_set_scope.
Notation "[ 'set' E | x 'in' A & y 'in' B ]" :=
  [set z | exists2 x, A x & exists2 y, B y & E = z] : classical_set_scope.

Definition image {A B} (f : A -> B) (X : set A) : set B :=
  [set f a | a in X].

Definition preimage {A B} (f : A -> B) (X : set B) : set A := [set a | X (f a)].
Arguments preimage A B f X / a.

Definition setT {A} := [set _ : A | True].
Definition set0 {A} := [set _ : A | False].
Definition set1 {A} (x : A) := [set a : A | x = a].
Definition setI {A} (X Y : set A) := [set a | X a /\ Y a].
Definition setU {A} (X Y : set A) := [set a | X a \/ Y a].
Definition setV {A B} (X : set A) (Y : set B) :=
  [set a : A + B | sum_rect _ X Y a].
Definition settt : set unit := setT.
Definition nonempty {A} (X : set A) := exists x, X x.
Definition setC {A} (X : set A) := [set a | ~ X a].
Definition setD {A} (X Y : set A) := [set a | X a /\ ~ Y a].
Definition setM {A B} (X : set A) (Y : set B) := [set x | X x.1 /\ Y x.2].
Definition fst_set {A B} (X : set (A * B)) := [set x | exists y, X (x, y)].
Definition snd_set {A B} (X : set (A * B)) := [set y | exists x, X (x, y)].

Notation "[ 'set' 'of' F ]" := [set F i | i in setT] : classical_set_scope.
Notation "[ 'set' a ]" := (set1 a) : classical_set_scope.
Notation "[ 'set' a : T ]" := [set (a : T)] : classical_set_scope.
Notation "A `|` B" := (setU A B) : classical_set_scope.
Notation "a |` A" := ([set a] `|` A) : classical_set_scope.
Notation "[ 'set' a1 ; a2 ; .. ; an ]" :=
  (setU .. (a1 |` [set a2]) .. [set an]) : classical_set_scope.
Notation "A `&` B" := (setI A B) : classical_set_scope.
Notation "A `*` B" := (setM A B) : classical_set_scope.
Notation "A .`1" := (fst_set A) : classical_set_scope.
Notation "A .`2" := (snd_set A) : classical_set_scope.
Notation "~` A" := (setC A) : classical_set_scope.
Notation "[ 'set' ~ a ]" := (~` [set a]) : classical_set_scope.
Notation "A `\` B" := (setD A B) : classical_set_scope.
Notation "A `\ a" := (A `\` [set a]) : classical_set_scope.

Definition bigsetI A I (P : set I) (X : I -> set A) :=
  [set a | forall i, P i -> X i a].
Definition bigsetU A I (P : set I) (X : I -> set A) :=
  [set a | exists2 i, P i & X i a].

Notation "\bigcup_ ( i 'in' P ) F" :=
  (bigsetU P (fun i => F)) : classical_set_scope.
Notation "\bigcup_ ( i : T ) F" :=
  (\bigcup_(i in @setT T) F) : classical_set_scope.
Notation "\bigcup_ i F" := (\bigcup_(i : _) F) : classical_set_scope.
Notation "\bigcap_ ( i 'in' P ) F" :=
  (bigsetI P (fun i => F)) : classical_set_scope.
Notation "\bigcap_ ( i : T ) F" :=
  (\bigcap_(i in @setT T) F) : classical_set_scope.
Notation "\bigcap_ i F" := (\bigcap_(i : _) F) : classical_set_scope.

Definition subset {A} (X Y : set A) := forall a, X a -> Y a.

Notation "A `<=` B" := (subset A B) : classical_set_scope.
Notation "A `<=>` B" := ((A `<=` B) /\ (B `<=` A)) : classical_set_scope.
Notation "f @^-1` A" := (preimage f A) : classical_set_scope.
Notation "f @` A" := (image f A) : classical_set_scope.
Notation "A !=set0" := (nonempty A) : classical_set_scope.

Definition graph_sym {T T'} (A : set (T * T')) :  set (T' * T) :=
  [set xy | A (xy.2, xy.1)].

Definition graph_comp {T' T T''} (A : set (T * T')) (B : set (T' * T'')) :
 set (T * T'') := [set xz | exists2 y, A (xz.1, y) & B (y, xz.2)].

Lemma eqEsubset T (F G : set T) : F `<=` G -> G `<=` F -> F = G.
Proof. by move=> H K; rewrite funeqE=> s; rewrite propeqE; split=> [/H|/K]. Qed.

Lemma sub0set T (X : set T) : set0 `<=` X.
Proof. by []. Qed.

Lemma subset0 T (X : set T) : (X `<=` set0) = (X = set0).
Proof. rewrite propeqE; split => [?|-> //]; exact/eqEsubset. Qed.

Lemma set0P T (X : set T) : (X <> set0) <-> (X !=set0).
Proof.
split=> [X_neq0|[t tX] X_eq0]; last by rewrite X_eq0 in tX.
apply: contrapT => /asboolPn/forallp_asboolPn X0.
by apply/X_neq0/eqEsubset.
Qed.

Lemma imageP {A B} (f : A -> B) (X : set A) a : X a -> (f @` X) (f a).
Proof. by exists a. Qed.

Lemma sub_image_setI {A B} (f : A -> B) (X Y : set A) :
  f @` (X `&` Y) `<=` f @` X `&` f @` Y.
Proof. by move=> b [x [Xa Ya <-]]; split; apply: imageP. Qed.
Arguments sub_image_setI {A B f X Y} a _.

Lemma nonempty_image {A B} (f : A -> B) (X : set A) :
  f @` X !=set0 -> X !=set0.
Proof. by case=> b [a]; exists a. Qed.

Lemma nonempty_preimage {A B} (f : A -> B) (X : set B) :
  f @^-1` X !=set0 -> X !=set0.
Proof. by case=> [a ?]; exists (f a). Qed.

Lemma preimage_image A B (f : A -> B) (X : set A) : X `<=` f@^-1` (f @` X).
Proof. by move=> a Xa; exists a. Qed.

Lemma image_preimage A B (f : A -> B) (X : set B) :
  f @` setT = setT -> f @` (f @^-1` X) = X.
Proof.
move=> fsurj; rewrite predeqE => x; split; first by move=> [?? <-].
move=> Xx; have : setT x by []; rewrite -fsurj => -[y _ fy_eqx].
by exists y => //; rewrite /preimage/mkset fy_eqx.
Qed.

Lemma preimage_setC A B (f : A -> B) (X : set B) :
  ~` (f @^-1` X) = f @^-1` (~` X).
Proof. by rewrite predeqE => a; split=> nXfa ?; apply: nXfa. Qed.

Lemma subset_empty {A} (X Y : set A) : X `<=` Y -> X !=set0 -> Y !=set0.
Proof. by move=> sXY [x Xx]; exists x; apply: sXY. Qed.

Lemma subset_trans {A} (Y X Z : set A) : X `<=` Y -> Y `<=` Z -> X `<=` Z.
Proof. by move=> sXY sYZ ? ?; apply/sYZ/sXY. Qed.

Lemma nonempty_preimage_setI {A B} (f : A -> B) (X Y : set B) :
  (f @^-1` (X `&` Y)) !=set0 <-> (f @^-1` X `&` f @^-1` Y) !=set0.
Proof. by split; case=> x ?; exists x. Qed.

Lemma subsetC {A} (X Y : set A) : X `<=` Y -> ~` Y `<=` ~` X.
Proof. by move=> sXY ? nYa ?; apply/nYa/sXY. Qed.

Lemma subsetU {A} (X Y Z : set A) : X `<=` Z -> Y `<=` Z -> X `|` Y `<=` Z.
Proof. by move=> sXZ sYZ a; apply: or_ind; [apply: sXZ|apply: sYZ]. Qed.

Lemma subUset T (X Y Z : set T) : (Y `|` Z `<=` X) = ((Y `<=` X) /\ (Z `<=` X)).
Proof.
rewrite propeqE; split => [|[YX ZX] x]; last by case; [exact: YX | exact: ZX].
by move=> sYZ_X; split=> x ?; apply sYZ_X; [left | right].
Qed.

Lemma subsetI A (X Y Z : set A) : (X `<=` Y `&` Z) = ((X `<=` Y) /\ (X `<=` Z)).
Proof.
rewrite propeqE; split=> [H|[y z ??]]; split; by [move=> ?/H[]|apply y|apply z].
Qed.

Lemma subIset {A} (X Y Z : set A) : X `<=` Z \/ Y `<=` Z -> X `&` Y `<=` Z.
Proof. case => H a; by [move=> [/H] | move=> [_ /H]]. Qed.

Lemma setD_eq0 A (X Y : set A) : (X `\` Y = set0) = (X `<=` Y).
Proof.
rewrite propeqE; split=> [XDY0 a|sXY].
  by apply: contrapTT => nYa xA; rewrite -[False]/(set0 a) -XDY0.
by rewrite predeqE => ?; split=> // - [?]; apply; apply: sXY.
Qed.

Lemma setDE {A} (X Y : set A) : X `\` Y = X `&` ~` Y.
Proof. by []. Qed.

Lemma setIid {A} (X : set A) : X `&` X = X.
Proof. by rewrite predeqE => ?; split=> [[]|]. Qed.

Lemma setIC {A} (X Y : set A) : X `&` Y = Y `&` X.
Proof. by rewrite predeqE => ?; split=> [[]|[]]. Qed.

Lemma setIT {A} (X : set A) : X `&` setT = X.
Proof. by rewrite predeqE => ?; split=> [[]|]. Qed.

Lemma setI0 {A} (X : set A) : X `&` set0 = set0.
Proof. by rewrite predeqE => ?; split=> [[]|]. Qed.

Lemma set0I A (Y : set A) : set0 `&` Y = set0.
Proof. by rewrite setIC setI0. Qed.

Lemma setIA {A} (X Y Z : set A) : X `&` (Y `&` Z) = X `&` Y `&` Z.
Proof. by rewrite predeqE => ?; split=> [[? []]|[[]]]. Qed.

Lemma setICA {A} (X Y Z : set A) : X `&` (Y `&` Z) = Y `&` (X `&` Z).
Proof. by rewrite setIA [X `&` _]setIC -setIA. Qed.

Lemma setIAC {A} (X Y Z : set A) : X `&` Y `&` Z = X `&` Z `&` Y.
Proof. by rewrite setIC setICA setIA. Qed.

Lemma setIACA {A} (X Y Z T : set A) :
  X `&` Y `&` (Z `&` T) = X `&` Z `&` (Y `&` T).
Proof. by rewrite -setIA [Y `&` _]setICA setIA. Qed.

Lemma setUA A : associative (@setU A).
Proof. by move=> p q r; rewrite /setU /mkset predeqE => a; tauto. Qed.

Lemma setUid A : idempotent (@setU A).
Proof. move=> p; rewrite /setU predeqE /mkset => a; tauto. Qed.

Lemma setUC A : commutative (@setU A).
Proof. move=> p q; rewrite /setU predeqE /mkset => a; tauto. Qed.

Lemma set0U T (X : set T) : set0 `|` X = X.
Proof. by rewrite funeqE => t; rewrite propeqE; split; [case|right]. Qed.

Lemma setU0 T (X : set T) : X `|` set0 = X.
Proof. by rewrite funeqE => t; rewrite propeqE; split; [case|left]. Qed.

Lemma setU_eq0 T (X Y : set T) : (X `|` Y = set0) = ((X = set0) /\ (Y = set0)).
Proof. by rewrite -!subset0 subUset. Qed.

Lemma setI_bigcapr A I (D : set I) (f : I -> set A) (X : set A) :
  X `&` \bigcap_(i in D) f i =
  \bigcap_(i in setV settt D) sum_rect (fun=> set A) (fun=> X) f i.
Proof.
rewrite predeqE => a; split; first by move=> [Xa IDfa] [[]|i]//= /IDfa.
move=> IXDfa; split; first by apply: (IXDfa (inl tt)).
by move=> i Di; apply: (IXDfa (inr i)).
Qed.

Lemma setI_bigcupl A I (D : set I) (f : I -> set A) (X : set A) :
 \bigcup_(i in D) f i `&` X = \bigcup_(i in D) (f i `&` X).
Proof.
rewrite predeqE => a; split => [[[i Di] fia] Xa|[i Di [fia Xa]]].
  by exists i.
by split=> //; exists i.
Qed.

Lemma setI_bigcupr A I (D : set I) (f : I -> set A) (X : set A) :
  X `&` \bigcup_(i in D) f i = \bigcup_(i in D) (X `&` f i).
Proof.
rewrite setIC setI_bigcupl; congr bigsetU.
by rewrite funeqE => i; rewrite setIC.
Qed.

Lemma setU_bigcapl A I (D : set I) (f : I -> set A) (X : set A) :
  \bigcap_(i in D) f i `|` X = \bigcap_(i in D) (f i `|` X).
Proof.
rewrite predeqE => a; split => [|fI].
  by move=> [fI|] i Di; [left; apply: fI|right].
by have [Xa|Xna] := asboolP (X a); [right |left => i /fI[]].
Qed.

Lemma setU_bigcapr A I (D : set I) (f : I -> set A) (X : set A) :
   X `|` \bigcap_(i in D) f i = \bigcap_(i in D) (X `|` f i).
Proof.
rewrite setUC setU_bigcapl; congr bigsetI.
by rewrite funeqE => i; rewrite setUC.
Qed.

Lemma bigcup_set1 {A I} (D : set I) (f : I -> set A) :
 \bigcup_(i in D) [set f i] = [set f i | i in D].
Proof. by []. Qed.

Lemma bigcup_map {A I J} (D : set I) (h : I -> J) (f : J -> set A) :
  \bigcup_(i in D) f (h i) = \bigcup_(j in [set h i | i in D]) f j.
Proof.
rewrite predeqE => a; split=> [[i Di]|[_ [i Di <-]]] fhia; last by exists i.
by exists (h i) => //; exists i.
Qed.

Lemma bigcup_bigcup {A I J}
    (DI : set I) (DJ : I -> set J) (f : J -> set A) :
  \bigcup_(j in \bigcup_(i in DI) DJ i) f j =
  \bigcup_(i in DI) \bigcup_(j in DJ i) f j.
Proof.
rewrite predeqE=> a; split => [[j [i Di Dij fja]]|[i Di [j Dij fja]]].
  by exists i => //; exists j.
by exists j => //; exists i.
Qed.

Lemma bigcap_bigcup {A I J}
    (DI : set I) (DJ : I -> set J) (f : J -> set A) :
  \bigcap_(j in \bigcup_(i in DI) DJ i) f j =
  \bigcap_(i in DI) \bigcap_(j in DJ i) f j.
Proof.
rewrite predeqE=> a; split=> [UUfa i Di j Dij|UUfa j [i Di Dij]].
  by apply: UUfa; exists i.
exact: UUfa Dij.
Qed.

Lemma bigcupM {I J A} (DI : set I) (DJ : set J) (f : I -> J -> set A) :
  \bigcup_(i in DI `*` DJ) f i.1 i.2 =
  \bigcup_(i in DI) \bigcup_(j in DJ) f i j.
Proof.
rewrite predeqE => i /=.
split=> [[[a b] [/=Da Db] fabj]|[a Da [b Db fabi]]]; last by exists (a, b).
by exists a => //; exists b => //.
Qed.

Definition is_singleton {A} (X : set A) := forall x y, X x -> X y -> x = y.
Definition is_fun {A B} (f : A -> B -> Prop) := all (is_singleton \o f).
Definition is_total {A B} (f : A -> B -> Prop) := all (nonempty \o f).
Definition is_totalfun {A B} (f : A -> B -> Prop) :=
  forall x, nonempty (f x) /\ is_singleton (f x).

Record is_filter {T} (F : set (set T)) := IsFilter {
  filterT : F setT ;
  filterI : forall P Q : set T, F P -> F Q -> F (setI P Q) ;
  filterS : forall P Q : set T, P `<=` Q -> F P -> F Q;
  filter_not_empty : not (F (fun _ => False)) ;
}.

Definition xget {T} x0 (P : set T) : T :=
  if pselect (exists x : T, `[<P x>]) isn't left exP then x0
  else projT1 (cid exP).

CoInductive xget_spec {T} x0 (P : set T) : T -> Prop -> Type :=
| XGetSome x of x = xget x0 P & P x : xget_spec x0 P x True
| XGetNone of (forall x, ~ P x) : xget_spec x0 P x0 False.

Lemma xgetP {T} x0 (P : set T) : xget_spec x0 P (xget x0 P) (P (xget x0 P)).
Proof.
move: (erefl (xget x0 P)); set y := {2}(xget x0 P).
rewrite /xget; case: pselect => /= [?|neqP _].
  by case: cid => x /= /asboolP Px; rewrite [P x]propT //; constructor.
suff NP x : ~ P x by rewrite [P x0]propF //; constructor.
by apply: contrap neqP => Px; exists x; apply/asboolP.
Qed.

Lemma xgetPex {T} x0 (P : set T) : (exists x, P x) -> P (xget x0 P).
Proof. by case: xgetP=> // NP [x /NP]. Qed.

Lemma xgetI {T} x0 (P : set T) (x : T): P x -> P (xget x0 P).
Proof. by move=> Px; apply: xgetPex; exists x. Qed.

Lemma xget_prop {T : nonPropType} x0 (P : set T) (x : T) :
  P x -> is_singleton P -> xget x0 P = x.
Proof. by move=> Px /(_ _ _ (xgetI x0 Px) Px). Qed.

Lemma xget_unique {T} x0 (P : set T) (x : T) :
  P x -> (forall y, P y -> y = x) -> xget x0 P = x.
Proof. by move=> /xget_prop gPx eqx; apply: gPx=> y z /eqx-> /eqx. Qed.

Lemma xgetPN {T} x0 (P : set T) : (forall x, ~ P x) -> xget x0 P = x0.
Proof. by case: xgetP => // x _ Px /(_ x). Qed.

Definition fun_of_graph {A} {B} (f0 : A -> B) (f : A -> B -> Prop) :=
  fun x => xget (f0 x) (f x).

Lemma fun_of_graphP {A} {B } (f : A -> B -> Prop) (f0 : A -> B) a :
  nonempty (f a) ->  f a (fun_of_graph f0 f a).
Proof. by move=> [b fab]; rewrite /fun_of_graph; apply: xgetI fab. Qed.

Lemma fun_of_graph_uniq {A} {B } (f : A -> B -> Prop) (f0 : A -> B) a :
  is_singleton (f a) -> forall b, f a b ->  fun_of_graph f0 f a = b.
Proof. by move=> fa_prop b /xget_prop xgeteq; rewrite /fun_of_graph xgeteq. Qed.

Definition total_on T (A : set T) (R : T -> T -> Prop) :=
  forall s t, A s -> A t -> R s t \/ R t s.

Section ZL.

Variable (T : Type) (t0 : T) (R : T -> T -> Prop).
Hypothesis (Rrefl : forall t, R t t).
Hypothesis (Rtrans : forall r s t, R r s -> R s t -> R r t).
Hypothesis (Rantisym : forall s t, R s t -> R t s -> s = t).
Hypothesis (tot_lub : forall A : set T, total_on A R -> exists t,
  (forall s, A s -> R s t) /\ forall r, (forall s, A s -> R s r) -> R t r).
Hypothesis (Rsucc : forall s, exists t, R s t /\ s <> t /\
  forall r, R s r -> R r t -> r = s \/ r = t).

Notation get := (xget t0).
Notation getPex := (xgetPex t0).

Let lub := fun A : {A : set T | total_on A R} =>
  get (fun t : T => (forall s, sval A s -> R s t) /\
    forall r, (forall s, sval A s -> R s r) -> R t r).
Let succ := fun s => get (fun t : T => R s t /\ s <> t /\
  forall r, R s r -> R r t -> r = s \/ r = t).

Inductive tower : set T :=
  | Lub : forall A, sval A `<=` tower -> tower (lub A)
  | Succ : forall t, tower t -> tower (succ t).

Lemma ZL' : False.
Proof.
have lub_ub (A : {A : set T | total_on A R}) :
  forall s, sval A s -> R s (lub A).
  suff /getPex [] : exists t : T, (forall s, sval A s -> R s t) /\
    forall r, (forall s, sval A s -> R s r) -> R t r by [].
  by apply: tot_lub; apply: (svalP A).
have lub_lub (A : {A : set T | total_on A R}) :
  forall t, (forall s, sval A s -> R s t) -> R (lub A) t.
  suff /getPex [] : exists t : T, (forall s, sval A s -> R s t) /\
    forall r, (forall s, sval A s -> R s r) -> R t r by [].
  by apply: tot_lub; apply: (svalP A).
have RS s : R s (succ s) /\ s <> succ s.
  by have /getPex [? []] : exists t : T, R s t /\ s <> t /\
    forall r, R s r -> R r t -> r = s \/ r = t by apply: Rsucc.
have succS s : forall t, R s t -> R t (succ s) -> t = s \/ t = succ s.
  by have /getPex [? []] : exists t : T, R s t /\ s <> t /\
    forall r, R s r -> R r t -> r = s \/ r = t by apply: Rsucc.
suff Twtot : total_on tower R.
  have [R_S] := RS (lub (exist _ tower Twtot)); apply.
  by apply/Rantisym => //; apply/lub_ub/Succ/Lub.
move=> s t Tws; elim: Tws t => {s} [A sATw ihA|s Tws ihs] t Twt.
  case: (pselect (forall s, sval A s -> R s t)).
    by move=> ?; left; apply: lub_lub.
  move/asboolP; rewrite asbool_neg => /existsp_asboolPn [s /asboolP].
  rewrite asbool_neg => /imply_asboolPn [As nRst]; right.
  by have /lub_ub := As; apply: Rtrans; have [] := ihA _ As _ Twt.
suff /(_ _ Twt) [Rts|RSst] : forall r, tower r -> R r s \/ R (succ s) r.
    by right; apply: Rtrans Rts _; have [] := RS s.
  by left.
move=> r; elim=> {r} [A sATw ihA|r Twr ihr].
  case: (pselect (forall r, sval A r -> R r s)).
    by move=> ?; left; apply: lub_lub.
  move/asboolP; rewrite asbool_neg => /existsp_asboolPn [r /asboolP].
  rewrite asbool_neg => /imply_asboolPn [Ar nRrs]; right.
  by have /lub_ub := Ar; apply: Rtrans; have /ihA [] := Ar.
have [Rrs|RSsr] := ihr; last by right; apply: Rtrans RSsr _; have [] := RS r.
have : tower (succ r) by apply: Succ.
move=> /ihs [RsSr|]; last by left.
by have [->| ->] := succS _ _ Rrs RsSr; [right|left]; apply: Rrefl.
Qed.

End ZL.

Lemma exist_congr T (P : T -> Prop) (s t : T) (p : P s) (q : P t) :
  s = t -> exist P s p = exist P t q.
Proof. by move=> st; case: _ / st in q *; apply/congr1/Prop_irrelevance. Qed.

Lemma Zorn T (R : T -> T -> Prop) :
  (forall t, R t t) -> (forall r s t, R r s -> R s t -> R r t) ->
  (forall s t, R s t -> R t s -> s = t) ->
  (forall A : set T, total_on A R -> exists t, forall s, A s -> R s t) ->
  exists t, forall s, R t s -> s = t.
Proof.
move=> Rrefl Rtrans Rantisym Rtot_max.
set totR := ({A : set T | total_on A R}).
set R' := fun A B : totR => sval A `<=` sval B.
have R'refl A : R' A A by [].
have R'trans A B C : R' A B -> R' B C -> R' A C by apply: subset_trans.
have R'antisym A B : R' A B -> R' B A -> A = B.
  rewrite /R'; case: A; case: B => /= B totB A totA sAB sBA.
  by apply: exist_congr; rewrite predeqE=> ?; split=> [/sAB|/sBA].
have R'tot_lub A : total_on A R' -> exists t, (forall s, A s -> R' s t) /\
    forall r, (forall s, A s -> R' s r) -> R' t r.
  move=> Atot.
  have AUtot : total_on (\bigcup_(B in A) (sval B)) R.
    move=> s t [B AB Bs] [C AC Ct].
    have [/(_ _ Bs) Cs|/(_ _ Ct) Bt] := Atot _ _ AB AC.
      by have /(_ _ _ Cs Ct) := svalP C.
    by have /(_ _ _ Bs Bt) := svalP B.
  exists (exist _ (\bigcup_(B in A) sval B) AUtot); split.
    by move=> B ???; exists B.
  by move=> B Bub ? /= [? /Bub]; apply.
apply: contrapT => nomax.
have {nomax} nomax t : exists s, R t s /\ s <> t.
  have /asboolP := nomax; rewrite asbool_neg => /forallp_asboolPn /(_ t).
  move=> /asboolP; rewrite asbool_neg => /existsp_asboolPn [s].
  by move=> /asboolP; rewrite asbool_neg => /imply_asboolPn []; exists s.
have tot0 : total_on set0 R by [].
apply: (ZL' (exist _ set0 tot0)) R'tot_lub _ => // A.
have /Rtot_max [t tub] := svalP A; have [s [Rts snet]] := nomax t.
have Astot : total_on (sval A `|` [set s]) R.
  move=> u v [Au|<-]; last first.
    by move=> [/tub Rvt| ->]; right=> //; apply: Rtrans Rts.
  move=> [Av|<-]; [apply: (svalP A)|left] => //.
  by apply: Rtrans Rts; apply: tub.
exists (exist _ (sval A `|` [set s]) Astot); split; first by move=> ??; left.
split=> [AeAs|[B Btot] sAB sBAs].
  case: (pselect (sval A s)); first by move=> /tub Rst; apply/snet/Rantisym.
  by rewrite AeAs /=; apply; right.
case: (pselect (B s)) => [Bs|nBs].
  by right; apply: exist_congr; rewrite predeqE => r; split=> [/sBAs|[/sAB| <-]].
left; case: A tub Astot sBAs sAB => A Atot /= tub Astot sBAs sAB.
apply: exist_congr; rewrite predeqE => r; split=> [Br|/sAB] //.
by have /sBAs [|ser] // := Br; rewrite -ser in Br.
Qed.

Definition premaximal T (R : T -> T -> Prop) (t : T) :=
  forall s, R t s -> R s t.

Lemma ZL_preorder T (t0 : T) (R : T -> T -> Prop) :
  (forall t, R t t) -> (forall r s t, R r s -> R s t -> R r t) ->
  (forall A : set T, total_on A R -> exists t, forall s, A s -> R s t) ->
  exists t, premaximal R t.
Proof.
move=> Rrefl Rtrans tot_max.
set eqR := fun s t => R s t /\ R t s; set ceqR := fun s => [set t | eqR s t].
have eqR_trans r s t : eqR r s -> eqR s t -> eqR r t.
  by move=> [Rrs Rsr] [Rst Rts]; split; [apply: Rtrans Rst|apply: Rtrans Rsr].
have ceqR_uniq s t : eqR s t -> ceqR s = ceqR t.
  by rewrite predeqE => - [Rst Rts] r; split=> [[Rr rR] | [Rr rR]]; split;
    try exact: Rtrans Rr; exact: Rtrans rR _.
set ceqRs := ceqR @` setT; set quotR := sig ceqRs.
have ceqRP t : ceqRs (ceqR t) by exists t.
set lift := fun t => exist _ (ceqR t) (ceqRP t).
have lift_surj (A : quotR) : exists t : T, lift t = A.
  case: A => A [t Tt ctA]; exists t; rewrite /lift; case : _ / ctA.
  exact/congr1/Prop_irrelevance.
have lift_inj s t : eqR s t -> lift s = lift t.
  by move=> eqRst; apply/exist_congr/ceqR_uniq.
have lift_eqR s t : lift s = lift t -> eqR s t.
  move=> cst; have ceqst : ceqR s = ceqR t by have := congr1 sval cst.
  by rewrite [_ s]ceqst; split; apply: Rrefl.
set repr := fun A : quotR => xget t0 [set t : T | lift t = A].
have repr_liftE t : eqR t (repr (lift t))
  by apply: lift_eqR; have -> := xgetPex t0 (lift_surj (lift t)).
set R' := fun A B : quotR => R (repr A) (repr B).
have R'refl A : R' A A by apply: Rrefl.
have R'trans A B C : R' A B -> R' B C -> R' A C by apply: Rtrans.
have R'antisym A B : R' A B -> R' B A -> A = B.
  move=> RAB RBA; have [t tA] := lift_surj A; have [s sB] := lift_surj B.
  rewrite -tA -sB; apply: lift_inj; apply (eqR_trans _ _ _ (repr_liftE t)).
  have eAB : eqR (repr A) (repr B) by [].
  rewrite tA; apply: eqR_trans eAB _; rewrite -sB.
  by have [] := repr_liftE s.
have [A Atot|A Amax] := Zorn R'refl R'trans R'antisym.
  have /tot_max [t tmax] : total_on [set repr B | B in A] R.
    by move=> ?? [B AB <-] [C AC <-]; apply: Atot.
  exists (lift t) => B AB; have [Rt _] := repr_liftE t.
  by apply: Rtrans Rt; apply: tmax; exists B.
exists (repr A) => t RAt.
have /Amax <- : R' A (lift t).
  by have [Rt _] := repr_liftE t; apply: Rtrans Rt.
by have [] := repr_liftE t.
Qed.
