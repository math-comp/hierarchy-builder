From Corelib Require Import ssreflect ssrfun.
From HB Require Import structures.

HB.mixin Record hasA T := { a : T }.
HB.structure Definition A := {T of hasA T}.

HB.mixin Record hasB (p : unit) T & A T := { b : T }.
HB.structure Definition B p := {T of A T & hasB p T}.

HB.mixin Record hasC (p q : unit) T & B p T := { c : T }.
HB.structure Definition C p q := {T of B p T & hasC p q T}.

Section test.
HB.declare Context p q T & hasA T & hasB p T & hasC p q T.
Definition test := [the C.type _ _ of T].
End test.

HB.factory Record hasABC (p q : unit) T := { a : T; b : T; c : T}.
HB.builders Context p q T & hasABC p q T.
HB.instance Definition _ := hasA.Build T a.
HB.instance Definition _ := hasB.Build p T b.
HB.instance Definition _ := hasC.Build p q T c.
HB.end.

Section test2.
HB.declare Context p q T & hasABC p q T.
Definition test2 := [the C.type _ _ of T].
End test2.

(* broken *)
(* Section test3.
Definition copy : Type -> Type := id.
HB.declare Context p T of hasABC p tt (copy T).
Definition test3 := [the C.type _ _ of copy T].
End test3. *)
