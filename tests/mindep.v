From HB Require Import structures.

HB.mixin Record m1 T := { t1 : T }.
HB.structure Definition Pointed1 := { T of m1 T }.

HB.mixin Record m2 T := { t2 : T }.
HB.structure Definition Pointed2 := { T of m2 T }.

HB.structure Definition Pointed12 := { T of m1 T & m2 T }.

HB.mixin Record m3 T := { t3 : T }.
HB.structure Definition TPointed123 := { T of m2 T & m1 T & m3 T }.

HB.mixin Record m4 T := { t4 : T }.
HB.structure Definition TPointed124 := { T of m2 T & m1 T & m4 T }.


HB.mixin Record m T of TPointed123 T := {
   p : t1 = t2 :> T 
}.                    
