From HB Require Import structures.
Require Import ssreflect ssrfun ssrbool.

HB.mixin Record HasMul T := {
  mul : T -> T -> T;
}.
HB.structure Definition Mul := { T of HasMul T }.

HB.mixin Record HasSq T := {
  sq : T -> T;
}.
HB.structure Definition Sq := { T of HasSq T }.

(* We need a functorial construction (a container)
   which preserves both structures. The simplest one is the option type. *)
Definition option_mul {T : Mul.type} (o1 o2 : option T) : option T :=
  match o1, o2 with
  | Some n, Some m => Some (mul n m)
  | _, _ => None
  end.
HB.instance Definition _ (T : Mul.type) := HasMul.Build (option T) option_mul.

Definition option_square {T : Sq.type} (o : option T) : option T :=
  match o with
  | Some n => Some (sq n)
  | None => None
  end.
HB.instance Definition _ (T : Sq.type) := HasSq.Build (option T) option_square.

(* Now we mix the two unrelated structures by building Sq out of Mul.
               *** This breaks Forgetful Inheritance ***
https://math-comp.github.io/competing-inheritance-paths-in-dependent-type-theory/
hence, HB prevents us from using it without care.
*)
Set Warnings "+HB.non-forgetful-inheritance".
Fail HB.instance Definition _ (T : Mul.type) :=
  HasSq.Build T (fun x => mul x x).

(* As advised by the error message, we contain the problem in a module *)
Module MulSq.
#[non_forgetful_inheritance]
HB.instance Definition _ (T : Mul.type) := HasSq.Build T (fun x => mul x x).

(* As we expect we can proved this (by reflexivity) *)
Lemma sq_mul (V : Mul.type) (v : V) : sq v = mul v v.
Proof. by reflexivity. Qed.

Lemma problem (W : Mul.type) (w : option W) : sq w = mul w w.
Proof.
Fail reflexivity. (* What? It used to work! *)
Fail rewrite sq_mul. (* Lemmas don't cross the container either! *)
(* Let's investigate *)
rewrite /mul/= /sq/=.
(* As we expect, we are on the option type. In the LHS it is the Sq built using
   the NFI instance
 
     option_square w = option_mul w w
*)
rewrite /option_mul/=.
rewrite /option_square/sq/=.
congr (match w with Some n => _ | None => None end).
(* The branches for Some differ, since w is a variable,
   they don't compare as equal

      (fun n : W => Some (mul n n)) =
      (fun n : W => match w with
                    | Some m => Some (mul n m)
                    | None => None
                    end)
*)
Abort.
End MulSq.