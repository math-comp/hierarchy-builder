From HB Require Import structures.

HB.mixin Record X_of_Type Ω := {}.
HB.structure Definition X := {Ω of X_of_Type Ω}.

HB.instance Definition XProp := X_of_Type.Build Prop.
Definition prop := Prop.
HB.instance Definition Xprop := X_of_Type.Build prop.

HB.instance Definition XSet := X_of_Type.Build Set.
Definition set := Set.
HB.instance Definition Xset := X_of_Type.Build set.

HB.instance Definition XType := X_of_Type.Build Type.
Definition type := Type.
HB.instance Definition Xtype := X_of_Type.Build type.
