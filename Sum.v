Require Import Nat.
Require Import Arith.

Inductive mynat: Set :=
  | O' : mynat (* zero *)
  | S' : mynat -> mynat (* 1 + mynat *)
  .


(* Proof something by induction.
2 * (sum 0 to n) = n (n + 1)

0 .. 10
pair them up
(1, 10) (2, 9) (3, 8)
all equal 11 or n + 1
there are n/2 number of these pairs
so 2 * (sum 0 to n) = n (n + 1) *)

Fixpoint sum_to_n (n: nat): nat :=
  match n with
  | O => 0
  | (S n') => n + sum_to_n n'
  end.

Theorem sum_to_n_shortcut_works: forall (n: nat),
  2 * sum_to_n n = n * (n + 1).
Proof.
induction n.
- simpl.
  reflexivity.
- (*
    above the line we have the induction hypothesis
    below the line we have the goal.
  *)
  unfold sum_to_n.
  fold sum_to_n.
  SearchRewrite (_ * (_ + _)).
  rewrite Nat.mul_add_distr_l.
  rewrite IHn.
  (* at this point the ring tactic is enough, but what if we don't use it. *)
  Search (?X + 1 = S ?X).
  repeat rewrite Nat.add_1_r.
  (* 2 * ?X + n * ?X *)
  Search (_ * ?X + _ * ?X).
  rewrite <- Nat.mul_add_distr_r.
  Check Nat.mul_comm.
  rewrite Nat.mul_comm with (n := (2 + n)).
  reflexivity.
Qed.

Theorem sum_to_n_shortcut_works_shorter: forall (n: nat),
  2 * sum_to_n n = n * (n + 1).
Proof.
induction n.
- simpl.
  reflexivity.
- unfold sum_to_n.
  fold sum_to_n.
  SearchRewrite (_ * (_ + _)).
  rewrite Nat.mul_add_distr_l.
  rewrite IHn.
  ring.
Qed.

Definition reverse {A: Type} (xs: list A) := xs.

Theorem double_reverse:
	forall (A: Type) (AS: list A),
	reverse (reverse AS) = AS.
Proof.