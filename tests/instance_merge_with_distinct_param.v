From HB Require Import structures.

HB.mixin Record m1 T := { default1 : T }.

HB.mixin Record m2 T := { default2 : T }.

HB.structure Definition s1 := { T of m1 T }.
HB.structure Definition s2 := { T of m2 T }.

HB.instance Definition _ (X : s1.type) : m1 (list X) :=
  m1.Build (list X) (cons default1 nil).
HB.instance Definition list_m2 (X : s2.type) : m2 (list X) :=
  m2.Build (list X) (cons default2 nil).

HB.structure Definition s3 := { T of m1 T & m2 T }.

Fail Check list nat:s3.type.

Fail Check fun t : s1.type => (list t : s3.type).
Fail Check fun t : s2.type => (list t : s3.type).
Check fun t : s3.type => (list t : s3.type).

