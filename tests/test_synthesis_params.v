From HB Require Import structures.

HB.mixin Record IsDualPOrdered (d : unit) T := {
  le : T -> T -> bool; ge : T -> T -> bool
}.

HB.structure Definition POrder d := { T of IsDualPOrdered d T }.

HB.factory Record IsPOrdered (d : unit) T := { le : T -> T -> bool }.

HB.builders Context d T & IsPOrdered d T.
HB.instance Definition _ := IsDualPOrdered.Build d T le le.
HB.end.

HB.mixin Record HasBottom d T & IsDualPOrdered d T := { bottom : T }.

HB.structure Definition BPOrder d := { T of HasBottom d T & IsDualPOrdered d T }.

HB.mixin Record HasTop d T & IsDualPOrdered d T := { top : T }.

HB.structure Definition TPOrder d := { T of HasTop d T & IsDualPOrdered d T }.

Definition dual (T : Type) := T.

Definition dd (d:unit) : unit. exact d. Qed.

HB.instance Definition _ d (T : POrder.type d) :=
  IsDualPOrdered.Build (dd d) (dual T) (fun x y => @le d T y x) (fun x y => @le d T y x).

HB.instance Definition _ d (T : TPOrder.type d) :=
  HasBottom.Build (dd d) (dual T) (@top _ T).

HB.instance Definition _ d (T : BPOrder.type d) :=
  HasTop.Build (dd d) (dual T) (@bottom _ T).

