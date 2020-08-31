(*
We can think of f as a type of maps from type A to type B.
*)
Theorem implication (A: Prop) (B: Prop):
  forall (f: A -> B) (a: A), B.
Proof.
(* intros brings the lambda abstraction into the hypothesis above the line *)
intros.
apply f.
exact a.
Qed.

Definition application (A: Set) (B: Set)
  (f: A -> B) (a: A): B :=
f a.

Theorem implication2a (P Q R: Prop):
  forall (f: P -> Q) (g: Q -> R), P -> R.
Proof.
intros f g p.
(* If we need to prove R and
   we can go from Q -> R
   then we only need to prove Q *)
apply g.
(* If we need to prove Q and
   we can go from P -> Q
   then we only need to prove P *)
apply f.
(* but we have a P as an hypothesis *)
exact p.
Qed.

Theorem implication2b (P Q R: Prop):
  forall (f: P -> Q) (g: Q -> R), P -> R.
Proof.
intros f g p.
apply f in p.
apply g in p.
exact p.
Qed.

Definition application2 (P Q R: Set)
  (f: P -> Q) (g: Q -> R) (p: P): R :=
g (f p).

Theorem implication2c (P Q R: Prop):
  forall (f: P -> Q) (g: Q -> R), P -> R.
Proof.
intros f g.
exact (fun p =>
  g (f p)
).
Qed.

(* These are all the same `g (f p)` *)
Print implication2c.
Print implication2a.
Print application2.

Theorem implication2d (P Q R: Prop):
  forall (f: P -> Q) (g: Q -> R) (p: P), R.
Proof.
(* Some tactics can do some types of reasoning for us. *)
auto.
(* The proof is irrelevant, we only care that it is true *)
Qed.

(* This is also the same `g (f p)` *)
Print implication2d.

Theorem conjunction (A: Prop) (B: Prop):
  forall (E: A /\ B), A.
Proof.
intros.
destruct E.
assumption.
Qed.

(* A * B = (A, B) *)
Definition product (A: Set) (B: Set)
  (pair: A * B): A :=
match pair with
  | (a, _) => a
end.

Theorem disjunction (A: Prop) (B: Prop):
  forall (b: B), A \/ B.
Proof.
intros.
right.
assumption.
Qed.

(* A + B = Either A B
   inl   = Left
   inr   = Right
*)
Definition sum (A: Set) (B: Set)
  (b: B): A + B :=
inr b.


