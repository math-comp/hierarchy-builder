From Coq Require Import ssreflect.
From HB Require Import structures.

HB.mixin Record isSigma (T : Type) (P : T -> Prop) (x : T) := {
  _ : P x
}.

#[short(type="sigType")]
HB.structure Definition Sig (T : Type) (P : T -> Prop) := {x of isSigma T P x}.

Section Sigma.

Check fun (T : Type) (P : T -> Prop) (x : sigType T P) => x : T.
Check fun (T : Type) (P : T -> Prop) (x : T) (Px : Sig T P x) => x : sigType T P.
Fail Check fun (T : Type) (P : T -> Prop) (x : T) => x : sigType T P.

Axioms (A B B' C : Type) (AtoB : A -> B) (BtoB' : B -> B').
Axioms (P : A -> Prop) (CtoAP : C -> sigType A P). 
Coercion AtoB : A >-> B.
Coercion BtoB' : B >-> B'.
(* does postcompose automatically with Coq coercions*) 
Check fun (x : sigType A P) => x : B.
Check fun (x : sigType A P) => x : B'.

(* testing a Coq coercion to sigType *)
Coercion CtoAP : C >-> sigType.
Check fun (x : C) => x : sigType A P.

(* does not precompose automatically with Coq coercions *)
Fail Check fun (x : C) => x : A.
Check fun (x : C) => (x : sigType A P) : A.
Check fun (x : C) => (x : sigType A P) : B.

Axioms (x : A) (Px : Sig A P x).

(* should not work indeed *)
Fail Check (x : sigType A P).

(* this works though ...*)
Succeed Check (let Px' := Px in x : sigType A P).

HB.instance Definition _ := Px.
Fail Check x : sigType A P.

End Sigma.

HB.mixin Record isSigmaT (P : Type -> Prop) (x : Type) := { _ : P x }.
#[short(type="sigTType")]
HB.structure Definition SigT (P : Type -> Prop) := {x of isSigmaT P x}.

Section SigmaT.

Axioms (X : Type) (PT : Type -> Prop) (PX : SigT PT X).

(* should not work indeed *)
Fail Check (X : sigTType PT).

(* this works though now ... cf my next point*)
Succeed Check (let PX' := PX in X : sigTType PT).

(* Now this works *)
HB.instance Definition _ := PX.
Succeed Check X : sigTType PT.

End SigmaT.
