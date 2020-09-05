Require Import Nat.
Require Import Arith.

Inductive mynat: Set :=
  | O' : mynat (* zero *)
  | S' : mynat -> mynat (* 1 + mynat *)
  .

Fixpoint sum_to_n (n: nat): nat :=
  match n with
  | O => 0
  | (S n') => n + sum_to_n n'
  end.

Ltac step X :=
  unfold X; fold X.

(* Proof something by induction.
2 * (sum 0 to n) = n (n + 1)

0 .. 10
pair them up
(1, 10) (2, 9) (3, 8)
all equal 11 or n + 1
there are n/2 number of these pairs
so 2 * (sum 0 to n) = n (n + 1) *)

Theorem sum_to_n_shortcut_works: forall (n: nat),
  2 * sum_to_n n = n * S n.
Proof.
(* Let us demo induction by doing induction on n *)
induction n.
- (* Lets simplify *)
  simpl.
  (* Easy *)
  reflexivity.
- (*
    above the line we have the induction hypothesis
    below the line we have the goal.
  *)
  (*
    does not seem like we can use the induction hypothesis yet
    Lets make sum_to_n take a single step
  *)
  step sum_to_n.
  (*
  Now we want redistribute `2 *` over
  `S n` and `sum_to_n n` respectively.
  There should be proof somewhere.
  Lets Search for it.
  *)
  SearchRewrite (_ * (_ + _)).
  (* Lets use this proof to rewrite our goal *)
  rewrite Nat.mul_add_distr_l.
  (* Now we can see our induction hypothesis *)
  rewrite IHn.
  (* We want to undistribute
     2 * S n + n * S n
     to be
     (2 + n) * S n
     Factor out the S n
  *)
  Search (_ * ?X + _ * ?X).
  (* We want to rewrite in the opposite direction *)
  rewrite <- Nat.mul_add_distr_r.
  (*
    I want to swap the multiplication using commutativity.
    I guess it might be call mul_comm, but lets check.
  *)
  Check Nat.mul_comm.
  (*
    Now lets rewrite and set the n variable to 2 + n.
  *)
  rewrite Nat.mul_comm with (n := (2 + n)).
  (*
    That is close enough,
    I think Coq can figure out this is equal
  *)
  reflexivity.
Qed.

(* This proof could also have been a lot shorter *)
Theorem sum_to_n_shortcut_works_shorter: forall (n: nat),
  2 * sum_to_n n = n * S n.
Proof.
induction n.
- reflexivity.
- step sum_to_n.
  rewrite Nat.mul_add_distr_l.
  rewrite IHn.
  ring.
Qed.
