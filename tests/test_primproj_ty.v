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

Set Printing All.

Goal let x := @addrA in True.
match goal with
| |- let x : forall s : AddMonoid.type, @associative (AddMonoid.sort s) (@add s) := @addrA in True => idtac "OK"
end.
Abort.
