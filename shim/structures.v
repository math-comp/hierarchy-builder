From Coq Require Import String ssreflect ssrfun.
Export String.StringSyntax.

Definition unify T1 T2 (t1 : T1) (t2 : T2) (s : option (string * Type)) :=
  phantom T1 t1 -> phantom T2 t2.
Definition id_phant {T} {t : T} (x : phantom T t) := x.
Definition nomsg : option (string * Type) := None.
Definition is_not_canonically_a : string := "is not canonically a".
Definition new {T} (x : T) := x.
