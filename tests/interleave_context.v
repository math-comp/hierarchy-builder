From Corelib Require Import ssreflect ssrfun ssrbool.
From HB Require Import structures.

HB.mixin Record HasA (n : nat) T := { a : T }.
HB.structure Definition A n := { T of HasA n T }.

HB.mixin Record HasB (X : A.type 0) (T : Type) := { b : X -> T }.
HB.structure Definition B (X : A.type 0) := { T of HasB X T }.

(* Since `B` expects an argument of type `A.type 0` (and not just
   just the naked type `T`) we pass `A.clone 0 T _`
   (of type `A.type 0`) and inference uses the first
   parameter `A` to elaborate it. *)
HB.mixin Record IsSelfA T & A 0 T & B (A.clone 0 T _) T := {}.

HB.structure Definition SelfA := { T of IsSelfA T }.

HB.factory Record IsSelfA' T := { a : T ; b : T -> T}.
HB.builders Context T & IsSelfA' T.
  HB.instance Definition _ := HasA.Build 0 T a.
  HB.instance Definition _ := HasB.Build _ T b.
  HB.instance Definition _ := IsSelfA.Build T.
HB.end.

HB.instance Definition _ := IsSelfA'.Build nat 0 id.
