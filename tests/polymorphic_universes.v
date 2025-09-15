From HB Require Import structures.
Set Universe Polymorphism.
Set Printing Universes.
#[verbose]
HB.mixin Record isA T := {}.

About isA.phant_axioms.

About isA.axioms_.
HB.structure Definition A := {T of isA T}.
