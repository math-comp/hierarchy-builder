From HB Require Import structures.

HB.lock Definition foo := 3.

Definition nat1 := nat.

HB.lock Definition bar : nat1 := 3.

HB.lock Definition baz n : nat := 3 + n.
