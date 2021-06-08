From HB Require Import structures.

Definition comb A op := forall x : A, op (op x) = x.

HB.mixin Record Foo A := {
  op : A -> A;
  ax : comb A op
}.

HB.structure Definition S := { A of Foo A }.

Set Printing All.
Lemma test1 : True.
Proof.
pose proof @ax as H.
match goal with
| H : forall x : S.type, comb (S.sort x) op |- _ => trivial
| H : ?T |- _ => fail "type of ax not as nice as expected:" T
end.
Qed.

HB.mixin Record HasMul T := {
  mul : T -> T -> T;
  mulC: forall x y : T, mul x y = mul y x;
  mulA: forall x y z : T, mul x (mul y z) = mul (mul x y) z;
}.
HB.structure Definition Mul := { T of HasMul T }.
Lemma test2 : True.
Proof.
pose proof @mulA as H.
match goal with
| H : forall s : Mul.type, forall x y z : Mul.sort s, mul x (mul y z) = mul (mul x y) z  |- _ => trivial
| H : ?T |- _ => fail "type of mulA not as nice as expected:" T
end.
Qed.
