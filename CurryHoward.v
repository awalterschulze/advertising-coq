(*
Given an A and a map from A to B,
then we can deduce B, using natural deduction.

A     A -> B
------------
    B

We can prove this in Coq.
*)
Theorem implication (A: Prop) (B: Prop):
  forall (f: A -> B) (a: A), B.
Proof.
(* intros brings the lambda abstraction into the hypothesis above the line *)
intros.
(* Now can apply f to the goal
   If we need to prove B,
   but we have a mapping from A to B,
   then technically we just need to prove A.
*)
apply f.
(*
  But we have an inhabitant of A, called a.
*)
exact a.
Qed.

(* 
   Programmers might just know this as
   function application.
   Coq type checks this function,
   so we know that it is correct.
*)
Definition application {A: Set} {B: Set}
  (f: A -> B) (a: A): B :=
f a.

(*
We do a little more complex implication.
If we have a map from P to Q and Q to R,
then we can decude a mapping from P to R.

P -> Q    Q -> R
----------------
     P -> R
*)
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

(* We can also do forwards instead of
   backwards reasoning
*)
Theorem implication2b (P Q R: Prop):
  forall (f: P -> Q) (g: Q -> R), P -> R.
Proof.
intros f g p.
(* lets apply f in p to get Q *)
apply f in p.
(* now lets apply g in p to get R *)
apply g in p.
(* now we have R *)
assumption.
Qed.

(* Again to programmers this is just
   function application
*)
Definition application2 (P Q R: Prop)
  (f: P -> Q) (g: Q -> R): P -> R :=
fun p => g (f p).

(*
We can combine the two in the same proof,
because the Curry-Howard Isomorphism says they are the same.
*)
Theorem implication2c (P Q R: Prop):
  forall (f: P -> Q) (g: Q -> R), P -> R.
Proof.
intros f g.
exact (fun p =>
  g (f p)
).
Qed.

(*
Underneath all these tactics, they are just code.
When we Print our proofs and code they are all the same:
`g (f p)`
*)
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

(*
Given A and B, we can deduce A

A /\ B
-------
   A
*)
Theorem conjunction (A: Prop) (B: Prop):
  forall (pair: A /\ B), A.
Proof.
intros pair.
(*
If we squint this looks just like the `product` function below.
This is because logical conjunction is the same as:
products, pairs, tuples or records in programming.
*)
exact (
  match pair with
  | conj A _B => A
  end
).
Qed.

(* A * B = (A, B) *)
Definition product (A: Set) (B: Set)
  (pair: A * B): A :=
match pair with
  | (a, _) => a
end.

(*
If we have B then we can deduce A or B.

   B
-------
A \/ B
*)
Theorem disjunction (A: Prop) (B: Prop):
  forall (b: B), A \/ B.
Proof.
intros.
(*
If we squint this looks just like the `sum` function below.
This is because logical disjunction is the same as:
sum types, coproducts or algebriac data types in programming.
*)
exact (
  (* Right b *)
  or_intror b
).
Qed.

(* A + B = Either A B
   inl   = Left
   inr   = Right
*)
Definition sum (A: Set) (B: Set)
  (b: B): A + B :=
(* Right b *)
inr b.
