From HB Require Import structures.

HB.mixin Record base_m T := { A : T }.
HB.structure Definition base := { T of base_m T }.

HB.mixin Record child1_m T := { C1 : T }.
HB.structure Definition child1 := { T of base T & child1_m T }.

HB.mixin Record child2_m T := { C2 : T }.
HB.structure Definition child2 := { T of base T & child2_m T }.

Axiom ix : Type.
Definition vec T := ix -> T.

Section b.
Variable T : base.type.
HB.instance Definition v_base_m : base_m (vec T) :=
  base_m.Build _ (fun _ => A).
End b.

Section c1.
Variable T : child1.type.
HB.instance Definition v_child1_m : child1_m (vec T) :=
    child1_m.Build _ (fun _ => C1).
End c1.

Section c2.
Variable T : child2.type.

  HB.instance Definition v_child2_m : child2_m (vec T) :=
  child2_m.Build _ (fun _ => C2).

End c2.
