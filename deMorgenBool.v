Require Import Bool.

Definition not := negb.

Theorem deMorgen: forall x y:bool,
  not (x || y) = (not x) && (not y).
Proof.
intros.
(* We can start by destruct x into all its cases,
   Almost like a truth table for computer scientists.
   A very lame induction for mathematicians.
*)
destruct x.
- simpl.
  reflexivity.
(* Coq helps us remember all cases.
   The proof cannot complete,
   if we haven't proved it for all cases.
*)
- simpl.
  reflexivity.
Qed.


