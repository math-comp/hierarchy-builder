From HB Require Import structures.

HB.mixin Record isTop M := { }.
HB.structure Definition Top := {M of isTop M}.

HB.mixin Record isA1 M & Top M := { }.
HB.structure Definition A1 := {M of isA1 M & isTop M}.

HB.mixin Record isA2 M & Top M := { }.
HB.structure Definition A2 := {M of isA2 M & isTop M}.

HB.mixin Record isB1 M & A1 M := { }.
HB.structure Definition B1 := {M of isB1 M & }.

HB.mixin Record isB2 M & A2 M := { }.
HB.structure Definition B2 :=  {M of isB2 M & isA2 M }.

HB.structure Definition B2A1 := {M of B2 M & A1 M }.

Fail HB.structure Definition A2B1 := {M of A2 M & B1 M }.
