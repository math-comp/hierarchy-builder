From Coq Require Import ssreflect ssrfun ssrbool.
From HB Require Import structures.

(* without params *)
HB.mixin Record isInhab T := { x : T }.
HB.structure Definition Inhab := { T of isInhab T }.
Definition unit' := unit.

HB.instance Definition _ := isInhab.Build unit' tt.
Check Inhab.of unit'.
Fail Check Inhab.of unit.
HB.instance Definition _ := Inhab.copy unit unit'.
Check Inhab.of unit.

(* with params *)
HB.mixin Record isInhabIf (b : bool) (T : Type) :=
  { y : forall ph : phant T, (match b with true => T | false => unit end) }.
HB.structure Definition InhabIf b := { T of isInhabIf b T }.

Definition bool' := bool.
HB.instance Definition _ := isInhabIf.Build true bool' (fun=> false).
Check InhabIf.of bool'.
Fail Check InhabIf.of bool.
HB.instance Definition _ := InhabIf.copy bool bool'.
Check InhabIf.of bool.
Check (y (Phant bool) : bool).
