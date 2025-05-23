(*It seems, once a subject is linked with a wrapped mixin,
it can't be instantiated as an unwrapped subject*)

From HB Require Import structures.

HB.mixin Record Q T (f: T->T) := {
  q : unit
}.

HB.mixin Record hasSelfMap T := {
  selfmap : T -> T
}.

HB.structure Definition SelfMapped := {T of hasSelfMap T}.

(* Comment this to avoid the fail, from here *)

  #[wrapper]
  HB.mixin Record Q__on__SelfMapped_selfmap T of SelfMapped T := {
    private : Q T selfmap
  }.

  HB.structure Definition QSelfMapped := {T of hasSelfMap T & Q__on__SelfMapped_selfmap T}.

(* to here *)

HB.instance Definition _ := hasSelfMap.Build nat (fun n => n).

Check @selfmap nat.

HB.mixin Record hasLaw T (x: T->T) := {
  law : unit
}.

HB.structure Definition Law T := {x of hasLaw T x}.

(*BUG: this should work*)
Fail HB.instance Definition _ := hasLaw.Build nat (@selfmap nat) tt.

Check @law nat _.
