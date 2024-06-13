From Coq Require Import ssreflect ssrfun.
From HB Require Import structures.

#[primitive]
HB.mixin Record AddMonoid_of_TYPE S := {
  zero : S;
  add : S -> S -> S;
  addrA : associative add;
  add0r : left_id zero add;
  addr0 : right_id zero add;
}.

HB.structure Definition AddMonoid := { A of AddMonoid_of_TYPE A }.

Goal let x := @addrA in True.
match goal with
| |- let x : forall s : AddMonoid.type, @associative (AddMonoid.sort s) (@add s) := @addrA in True => idtac "OK"
end.
Abort.

#[primitive]
HB.mixin Record Scale_of_AddMonoid (P : Type) S of AddMonoid_of_TYPE S := {
  scale : P -> S -> S;
  scaleBad : forall p (x y : S), (* HUMMM, if I don't put S here, it infers the eta expansion of S *)
    scale p (add x y) = add (scale p x) (scale p y);
}.

About Scale_of_AddMonoid.scale.

HB.structure Definition ScaleMonoid P := { A of Scale_of_AddMonoid P A }.

Goal let a := @scaleBad in True.
match goal with
| |- let a : forall P (s : ScaleMonoid.type P), forall p : P, forall x y : ScaleMonoid.sort P s, scale p (add x y) = add (scale p x) (scale p y) := @scaleBad in True => idtac "OK"
end.
Abort.

