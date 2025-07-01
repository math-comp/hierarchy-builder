From HB Require Import structures.
Set Universe Polymorphism.

HB.mixin Record isA T := {}.
HB.structure Definition A := {T of isA T}.
