From HB Require Import structures.

HB.mixin Record IsPOrdered (d : unit) T := {
  le : T -> T -> bool; ge : T -> T -> bool
}.

HB.structure Definition POrder d := { T of IsPOrdered d T }.

HB.mixin Record HasPoint T := { point : T }.

HB.structure Definition PPOrder d := { T of HasPoint T & IsPOrdered d T }.

HB.mixin Record HasBottom d T of IsPOrdered d T := { bottom : T }.

HB.structure Definition BPOrder d := { T of HasBottom d T & IsPOrdered d T }.

HB.structure Definition BPPOrder d := { T of HasPoint T & BPOrder d T }.

HB.mixin Record HasTop d T of IsPOrdered d T := { top : T }.

HB.structure Definition TPOrder d := { T of HasTop d T & IsPOrdered d T }.

HB.structure Definition TPPOrder d := { T of HasPoint T & TPOrder d T }.

Definition dual (T : Type) := T.

Definition dd (d:unit) : unit. exact d. Qed.

HB.instance Definition _ d (T : POrder.type d) :=
  IsPOrdered.Build (dd d) (dual T) (fun x y => @le d T y x) (fun x y => @le d T y x).

HB.instance Definition _ d (T : PPOrder.type d) :=
  HasPoint.Build (dual T) (@point _ T).

HB.instance Definition _ d (T : TPOrder.type d) :=
  HasBottom.Build (dd d) (dual T) (@top _ T).

HB.instance Definition _ d (T : TPPOrder.type d) :=
  BPOrder.on (dual T).

HB.instance Definition _ d (T : BPOrder.type d) :=
  HasTop.Build (dd d) (dual T) (@bottom _ T).

Fail HB.instance Definition _ d (T : BPPOrder.type d) :=
  TPOrder.on (dual T).
