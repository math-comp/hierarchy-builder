From HB Require Import structures.

HB.mixin Record isSomething T := { clearly : True }.
HB.structure Definition Something := { T of isSomething T }.

HB.mixin Record isSomethingElse (T : Type) := { p : True }.

HB.tag Definition tag1 (T : Something.type) : Type := T.

#[wrapper]
HB.mixin Record tag1_isSomethingElse T of Something T := {
  private : isSomethingElse (tag1 T)
}.

HB.tag Definition tag2 (T : Something.type) : Type := T.

#[wrapper]
HB.mixin Record tag2_isSomethingElse T of Something T := {
  private : isSomethingElse (tag2 T)
}.

(* This is a bug, maybe even in master. If I declare an instance on a mixin
   which leads to no new structure instance, then the mixin is not use later
   on *)
HB.structure Definition magic1 := { T of
  isSomething T &
  isSomethingElse (tag1 T)
}.

HB.structure Definition magic := { T of
  isSomething T &
  isSomethingElse (tag1 T) &
  isSomethingElse (tag2 T)
}.

HB.instance Definition _ : isSomething nat := isSomething.Build nat I.
HB.instance Definition _ : isSomethingElse (tag1 nat) := isSomethingElse.Build nat I.
HB.instance Definition _ : isSomethingElse (tag2 nat) := isSomethingElse.Build nat I.
Check nat : magic.type.
