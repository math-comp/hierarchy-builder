From HB Require Import structures.

HB.mixin Record isSomething T := { clearly : True }.
HB.structure Definition Something := { T of isSomething T }.

HB.mixin Record isTerminal (T : Type) := { p : True }.

HB.tag Definition this_one (T : Something.type) : Type := T.

#[wrapper]
HB.mixin Record this_one_isTerminal T of Something T := {
  private : isTerminal (this_one T)
}.

HB.tag Definition this_other_one (T : Something.type) : Type := T.

#[wrapper]
HB.mixin Record this_other_one_isTerminal T of Something T := {
  private : isTerminal (this_other_one T)
}.
(* This is a bug, maybe even in master. If I declare an instance on a mixin
   which leads to no new structure instance, then the mixin is not use later
   on *)
HB.structure Definition magic1 := { T of
  isSomething T &
  isTerminal (this_one T)
}.

HB.structure Definition magic := { T of
  isSomething T &
  isTerminal (this_one T) &
  isTerminal (this_other_one T)
}.

HB.instance Definition _ : isSomething nat := isSomething.Build nat I.
HB.instance Definition _ : isTerminal (this_one nat) := isTerminal.Build nat I.
HB.instance Definition _ : isTerminal (this_other_one nat) := isTerminal.Build nat I.
Check nat : magic.type.
