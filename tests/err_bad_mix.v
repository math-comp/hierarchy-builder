From HB Require Import structures.

Module Test.
  HB.mixin Record Mixin T := {
    zero: T;
  }.

  HB.structure Definition Struct := { T of Mixin T }.

  HB.instance Definition struct_bool := Mixin.Build bool true.

  Module Exports.
    HB.reexport.
  End Exports.
End Test.
(** Uncommenting any of these two prevents the issue *)
(* Export Test.Exports. *)
(* HB.export Test. *)

Fail HB.instance Definition struct_nat := Test.Mixin.Build nat 0.
