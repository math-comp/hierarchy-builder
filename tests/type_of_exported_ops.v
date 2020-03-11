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