From HB Require Import structures.

Variant testTy := A | B.
HB.mixin Record Stack1 T := { prop1 : unit }.
HB.structure Definition JustStack1 := { T of Stack1 T }.
HB.mixin Record Stack1Param R T := { prop2 : unit }.
HB.structure Definition JustStack1Param R := { T of Stack1Param R T }.

HB.mixin Record Stack2 T := { prop3 : unit }.
HB.structure Definition JustStack2 := { T of Stack2 T }.
HB.mixin Record Mixed T & Stack1 T & Stack2 T := { prop4 : unit }.
HB.structure Definition JustMixed := { T of Mixed T & Stack1 T & Stack2 T}.
HB.structure Definition JustMixedParam R := 
  { T of Mixed T & Stack1 T & Stack1Param R T & Stack2 T}.

HB.instance Definition _ := @Stack1.Build testTy tt.
HB.instance Definition _ := @Stack2.Build testTy tt.

HB.instance Definition _ {R} := @Stack1Param.Build R testTy tt.
HB.instance Definition _ := @Mixed.Build testTy tt.

Check testTy : JustMixedParam.type _.
