From HB Require Import structures.

HB.mixin Record m1 T := { default1 : T }.

HB.mixin Record m2 T := { default2 : T }.

(* since s1 only requires m1 there is a 1:1 correspondence 
between the structure s1 and the mixin m1 *)
HB.structure Definition s1 := { T of m1 T }.
HB.structure Definition s2 := { T of m2 T }.

HB.instance Definition nat_m1 := m1.Build nat 0.
HB.instance Definition nat_m2 := m2.Build nat 1.

(* with the following example we want to show that list
preserves the s1 structure ie. if x:s1.type then (list x):s1.type,
in practice we can use this for the type of polynomials *)
HB.instance Definition list_m1 (X : s1.type) : m1 (list X) :=
  m1.Build (list X) (cons default1 nil).
(* similarly list preserves s2 structure *)
HB.instance Definition list_m2 (X : s2.type) : m2 (list X) :=
  m2.Build (list X) (cons default2 nil).


HB.structure Definition s3 := { T of m1 T & m2 T }.
(* since we can preserve m1 and m2 with list, we can preserve s3 as well ! *)

(* 
if we have a file A with definitions of S1 and S2,
file B importing Awith definitions of instance nat_m1 and nat_m2
file C importing A with the definition of s3
in a file D that imports B and C if we call saturate_instance, we create the instance for s3.
this example shows the need for a separate command
*)
Fail Check nat : s3.type.
HB.saturate.
Check nat : s3.type.
(* since nat satisfies s3.type, so does list nat *)
Check list nat : s3.type.
Check list (list nat) : s3.type.

Fail Check fun t : s1.type => (list t : s3.type).
Fail Check fun t : s2.type => (list t : s3.type).
Check fun t : s3.type => (list t : s3.type).

HB.mixin Record m1' (P : s1.type) T := { f1 : P -> T }.

HB.mixin Record m2' (P : s2.type) T := { f2 : P -> T }.

(* since s1 only requires m1 there is a 1:1 correspondence 
between the structure s1 and the mixin m1 *)
HB.structure Definition s1' P := { T of m1' P T }.
HB.structure Definition s2' P := { T of m2' P T }.

HB.instance Definition nat_m1' := m1'.Build nat nat (fun _ => 0).
HB.instance Definition nat_m2' := m2'.Build nat nat (fun _ => 1).

(* with the following example we want to show that list
preserves the s1 structure ie. if x:s1.type then (list x):s1.type,
in practice we can use this for the type of polynomials *)
HB.instance Definition list_m1' (P : s1.type) (X : s1'.type P) : m1' P (list X) :=
m1'.Build P (list X) (fun x => cons (f1 x) nil).
(* similarly list preserves s2 structure *)
HB.instance Definition list_m2' (P : s2.type) (X : s2'.type P) : m2' P (list X) :=
  m2'.Build P (list X) (fun x => cons (f2 x) nil).


HB.structure Definition s3' (P : s3.type) := { T of m1' P T & m2' P T }.
Fail Check nat : s3'.type _.
HB.saturate.
Check nat : s3'.type _.
(* since nat satisfies s3'.type, so does list nat *)
Check list nat : s3'.type _.
Check Datatypes_list__canonical__two_hier_s3'.
Check list (list nat) : s3'.type _.