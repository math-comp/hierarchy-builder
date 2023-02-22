
From HB Require Import structures.
Require Import ssreflect ssrfun ssrbool.

(* ******************************************************************* *)
(* *********************** Hierarchy design ************************** *)
(* ******************************************************************* *)

Module BadInheritance.

HB.mixin Record HasMul T := {
  mul : T -> T -> T;
}.
HB.structure Definition Mul := { T of HasMul T }.

HB.mixin Record HasSq T := {
  sq : T -> T;
}.
HB.structure Definition Sq := { T of HasSq T }.

(* We need a functorial construction (a container)
   which preserves both structures. The simplest one is the option type. *)
Definition option_mul {T : Mul.type} (o1 o2 : option T) : option T :=
  match o1, o2 with
  | Some n, Some m => Some (mul n m)
  | _, _ => None
  end.
HB.instance Definition _ (T : Mul.type) := HasMul.Build (option T) option_mul.

Definition option_square {T : Sq.type} (o : option T) : option T :=
  match o with
  | Some n => Some (sq n)
  | None => None
  end.
HB.instance Definition _ (T : Sq.type) := HasSq.Build (option T) option_square.

(* Now we mix the two unrelated structures by building Sq out of Mul.

               *** This breaks Non Forgetful Inheritance ***
https://math-comp.github.io/competing-inheritance-paths-in-dependent-type-theory/

*)
#[non_forgetful_inheritance]
HB.instance Definition _ (T : Mul.type) := HasSq.Build T (fun x => mul x x).

(* As we expect we can proved this (by reflexivity) *)
Lemma sq_mul (V : Mul.type) (v : V) : sq v = mul v v.
Proof. by reflexivity. Qed.

Lemma problem (W : Mul.type) (w : option W) : sq w = mul w w.
Proof.
Fail reflexivity. (* What? It used to work! *)
Fail rewrite sq_mul. (* Lemmas don't cross the container either! *)
(* Let's investigate *)
rewrite /mul/= /sq/=.
(* As we expect, we are on the option type. In the LHS it is the Sq built using
   the NFI instance
 
     option_square w = option_mul w w
*)
rewrite /option_mul/=.
rewrite /option_square/sq/=.
congr (match w with Some n => _ | None => None end).
(* The branches for Some differ, since w is a variable,
   they don't compare as equal

      (fun n : W => Some (mul n n)) =
      (fun n : W => match w with
                    | Some m => Some (mul n m)
                    | None => None
                    end)
*)
Abort.

End BadInheritance.

Module GoodInheritance.

HB.mixin Record HasMul T := {
  mul : T -> T -> T;
}.
HB.structure Definition Mul := { T of HasMul T }.

HB.mixin Record HasSq T of Mul T := {
  sq : T -> T;
  sq_mul : forall x, sq x = mul x x;
}.
HB.structure Definition Sq := { T of HasSq T & Mul T }.

Definition option_mul {T : Mul.type} (o1 o2 : option T) : option T :=
  match o1, o2 with
  | Some n, Some m => Some (mul n m)
  | _, _ => None
  end.
HB.instance Definition _ (T : Mul.type) := HasMul.Build (option T) option_mul.

Definition option_square {T : Sq.type} (o : option T) : option T :=
  match o with
  | Some n => Some (sq n)
  | None => None
  end.
Lemma option_sq_mul {T : Sq.type} (o : option T) : option_square o = mul o o.
Proof. by rewrite /option_square; case: o => [x|//]; rewrite sq_mul. Qed.
HB.instance Definition _ (T : Sq.type) := HasSq.Build (option T) option_square option_sq_mul.

Lemma problem (W : Sq.type) (w : option W) : sq w = mul w w.
Proof. by rewrite sq_mul. Qed.

End GoodInheritance.

(* ******************************************************************* *)
(* ********************** Feather factories *********************** *)
(* ******************************************************************* *)

(*

  HB comes with a concept of factory, a virtual interface that is compiled
  down to the real ones.

  When the contents of a factory are just one lemma, the following trick
  may come handy.

  We define a type "link" which is convertible to a new type T but
  carries, as a dummy argument, a proof that T is linked to some known
  type xT. We can then use "link" to transfer (copy) structure instances
  across the link.

*)

Module Feather.

(* We need a hierarchy with a few structure, here we Equality -> Singleton *)
HB.mixin Record HasEqDec T := {
    eqtest : T -> T -> bool;
    eqOK : forall x y, reflect (x = y) (eqtest x y);
}.
HB.structure Definition Equality := { T of HasEqDec T }.

HB.mixin Record IsContractible T of HasEqDec T := {
    def : T;
    all_def : forall x, eqtest x def = true;
}.
HB.structure Definition Singleton := { T of IsContractible T }.

(*
   This is the type which is used as a feather factory.

   - xT plays the role of a rich type,
   - T is a new type linked to xT by some lemma. In this case a very strong
     cancellation lemma canfg
*)
Definition link {xT T : Type} {f : xT -> T} {g : T -> xT}
                (canfg : forall x, f (g x) = x)
              :=
                 T. (* (link canfg) is convertible to T *)

(* We explain HB how to transfer Equality over link *)
Section TransferEQ.

Context {eT : Equality.type} {T : Type} {f : eT -> T} {g : T -> eT}.
Context (canfg : forall x, f (g x) = x).

Definition link_eqtest (x y : T) : bool := eqtest (g x) (g y).

Lemma link_eqOK (x y : T) : reflect (x = y) (link_eqtest x y).
Proof.
rewrite /link_eqtest; case: (eqOK (g x) (g y)) => [E|abs].
  by constructor; rewrite -[x]canfg -[y]canfg E canfg.
by constructor=> /(f_equal g)/abs.
Qed.

(* (link canfg) is now an Equality instance *)
HB.instance Definition link_HasEqDec :=
  HasEqDec.Build (link canfg) link_eqtest link_eqOK.

End TransferEQ.

(* We explain HB how to transfer Singleton over link *)
Section TransferSingleton.

Context {eT : Singleton.type} {T : Type} {f : eT -> T} {g : T -> eT}.
Context (canfg : forall x, f (g x) = x).

Definition link_def : link canfg := f def.

Lemma link_all_def x : eqtest x link_def = true.
Proof.
rewrite /link_def; have /eqOK <- := all_def (g x).
by rewrite canfg; case: (eqOK x x).
Qed.

(* (link canfg) is now a Signleton instance *)
HB.instance Definition _ := IsContractible.Build (link canfg) link_def link_all_def.

End TransferSingleton.

(* We assume a known type B which is both an Equality and a Singleton *)
Axiom B : Type.

Axiom testB : B -> B -> bool.
Axiom testOKB : forall x y, reflect (x = y) (testB x y).
HB.instance Definition _ := HasEqDec.Build B testB testOKB.

Axiom defB : B.
Axiom all_defB : forall x, eqtest x defB = true.
HB.instance Definition _ := IsContractible.Build B defB all_defB.

(* Now we copy all instances from B to A via link *)
Axiom A : Type.
Axiom f : B -> A.
Axiom g : A -> B.
Axiom canfg : forall x, f (g x) = x.

(* We take all the instances up to Singleton on (link canfg) and we copy them
   on A. Recall (link canfg) is convertible to A *)
HB.instance Definition _ := Singleton.copy A (link canfg).

HB.about A. (* both Equality and Singleton have been copied *)

End Feather.

(* ******************************************************************* *)
(* ********************** Abstraction barriers *********************** *)
(* ******************************************************************* *)

Require Import Arith.

Module SlowFailure.

(* 
   When building a library it is natural to stack definitions up and reuse
   things you already have as much as possible.
   
   More often that not we want to set up abstraction barriers.
   For example one may define a mathematical concept using, say, lists and their
   operations, provide a few lemmas about the new concept, and then expect the
   user to never unfold the concept and work with lists directly.

   Abstraction barriers are not only good for clients, which are granted to work
   at the right abstraction level, but also for Coq itself, since it may be
   tricked into unfolding definitions and manipulate huge terms.

   HB.lock is a tool to easily impose abstraction barriers. It uses modules
   and module signatures to seal the body of a definition, keeping access to
   it via an equation.

*)

(* not a very clever construction, but a large one. Bare with us. *)
Definition new_concept := 999999.

Lemma test x : new_concept ^ x ^ new_concept = x ^ new_concept ^ new_concept.
Proof.
(* this goal is not trivial, and maybe even false, but you may call
   some automation on it anyway *)
Time Fail reflexivity. (* takes 7s, note that both by and // call reflexivity *)
Abort.

End SlowFailure.

(* cf https://github.com/coq/coq/issues/17223 *)
Optimize Heap.

Module FastFailure.

HB.lock Definition new_concept := 999999.

Lemma test x : new_concept ^ x ^ new_concept = x ^ new_concept ^ new_concept.
Time Fail reflexivity. (* takes 0s *)
rewrite new_concept.unlock.
Time Fail reflexivity. (* takes 7s, the original body is restored *)
Abort.

Print Module Type new_conceptLocked.
Print Module new_concept.
(*
   Module Type new_conceptLocked = Sig
     Parameter body : nat.
     Parameter unlock : body = 999999
   End
   Module new_concept : new_conceptLocked := ...
*)
Print new_concept.
(*
   Notation new_concept := new_concept.body
*)

Canonical unlock_new_concept := Unlockable new_concept.unlock.

End FastFailure.

(* ******************************************************************* *)
(* ******************************* Joins ***************************** *)
(* ******************************************************************* *)

(*

  All structures which are not leaves must be joinable

*)

Module MissingJoin.

HB.mixin Record isTop M := { }.
HB.structure Definition Top := {M of isTop M}.

HB.mixin Record isA1 M of Top M := { }.
HB.structure Definition A1 := {M of isA1 M & isTop M}.

HB.mixin Record isA2 M of Top M := { }.
HB.structure Definition A2 := {M of isA2 M & isTop M}.

HB.mixin Record isB1 M of A1 M := { }.
HB.structure Definition B1 := {M of isB1 M & }.

HB.mixin Record isB2 M of A2 M := { }.
HB.structure Definition B2 :=  {M of isB2 M & isA2 M }.

HB.structure Definition B2A1 := {M of B2 M & A1 M }.

Fail HB.structure Definition A2B1 := {M of A2 M & B1 M }.

HB.graph "missing_join.dot".

End MissingJoin.


Module GoodJoin.

HB.mixin Record isTop M := { }.
HB.structure Definition Top := {M of isTop M}.

HB.mixin Record isA1 M of Top M := { }.
HB.structure Definition A1 := {M of isA1 M & isTop M}.

HB.mixin Record isA2 M of Top M := { }.
HB.structure Definition A2 := {M of isA2 M & isTop M}.

HB.mixin Record isB1 M of A1 M := { }.
HB.structure Definition B1 := {M of isB1 M & }.

HB.mixin Record isB2 M of A2 M := { }.
HB.structure Definition B2 :=  {M of isB2 M & isA2 M }.

HB.structure Definition join := {M of A1 M & A2 M }.


HB.structure Definition B2A1 := {M of B2 M & A1 M }.
HB.structure Definition A2B1 := {M of A2 M & B1 M }.

HB.graph "good_join.dot".

End GoodJoin.
