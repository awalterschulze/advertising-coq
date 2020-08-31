Require Import Bool.

(* Please ignore:
   negb is just another name for
   the not function for booleans,
   more on that later.
*)
Definition not := negb.

Theorem deMorgen: forall x y:bool,
  not (x || y) = (not x) && (not y).
Proof.
intros.
(* We can start by destructing x into its two cases.
   Almost like a truth table for computer scientists or
   A very lame induction for mathematicians.
*)
destruct x.
(* Now we have two cases to prove,
   lets focus on our first goal
*)
- 
(* Seems like some of this equation is simply solvable *)
  simpl.
(* false = false is true by reflexivity *)
  reflexivity.
(* Coq helps us remember all cases.
   The proof cannot complete,
   if we haven't proved it for all cases.
*)
- (* seems like this can also be simplified *)
  simpl.
  (* not y = not y, no matter what y is *)
  reflexivity.
Qed.
(* Qed = Proven *)

