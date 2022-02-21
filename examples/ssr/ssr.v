From HB Require Import structures.
From Coq Require Import ssreflect ssrfun ssrbool.

Axiom propext : forall (P Q : Prop), (P <-> Q) -> P = Q.

HB.mixin Record HasEquality T := {
  eq_op : T -> T -> bool;
  eq_axiom : forall x y, reflect (x = y) (eq_op x y)
}.
HB.structure Definition Equality := {T of HasEquality T}.

Structure dProp := DProp {
  to_prop :> Prop;
  to_bool :> bool;
  to_propP : to_prop <-> to_bool = true
}.

Canonical eq_dprop (T : Equality.type) (x y : T) := 
  @DProp (x = y) (eq_op x y) (rwP (eq_axiom x y)).

Notation "[ x ]" := (x : dProp).

(* - Prop <- dProp -> bool *)
(* - A -> X <- B *)


Check fun (T : Equality.type) (x y : T) => if [ x = y ] then 1 else 0.

Program Canonical true_dprop :=
  @DProp True true _.
Next Obligation. Admitted.

Program Canonical and_dprop (P Q : dProp) :=
  @DProp (P /\ Q) (P && Q) _.
Next Obligation. Admitted.

Check fun (T : Equality.type) (x y : T) =>
  if [x = y /\ y = x] then 1 else 0.

Definition reduce (P Q : dProp) : solve (P = Q :> bool) -> P <-> Q.
Proof.
Admitted.

Lemma PT {P : Prop} : P -> P = True :> Prop.
Proof. by move=> p; apply: propext; split. Qed.

Lemma test (P Q : dProp) : P -> Q -> P /\ True /\ Q.
Proof.
move=> p q.
apply/reduce => /=.
  reflexivity.
rewrite /=.
done.
Restart.
move=> p q.
apply/to_propP => /=.
apply/to_propP => /=.
done.
Restart.
move=> p q /=.
rewrite (PT p) (PT q).
apply/to_propP => /=.
Qed.


(* Record hasN T := { *)
(*   inN : T -> DProp; *)
(*   N := {x : T | inN x = true}; *)
  
  
(*   natN : nat -> N; *)
(*   N0 : N; *)
(*   NS : N -> N; *)
(*   nat0 :; *)
(*   natS : forall x : N, inN (S x) *)
(* }. *)


(* Definition  *)

