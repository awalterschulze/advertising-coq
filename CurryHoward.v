(*
If we have a map from P to Q and Q to R,
then we can decude a mapping from P to R using natural deduction.

P -> Q    Q -> R
----------------
     P -> R

We can prove this in Coq.
*)
Theorem implication1 (P Q R: Prop):
  forall
  (f: P -> Q)
  (g: Q -> R),
  P ->
  R.
Proof.
intros f g p.
(* If we need to prove R and
   we know Q implies R
   then we only need to prove Q *)
apply g.
(* If we need to prove Q and
   we know P implies Q
   then we only need to prove P *)
apply f.
(* but we have a P as an hypothesis *)
exact p.
Qed.

(* We can also do forwards instead of
   backwards reasoning
*)
Theorem implication2 (P Q R: Prop):
  forall
  (f: P -> Q)
  (g: Q -> R),
  P ->
  R.
Proof.
intros f g p.
(* lets apply f in p, since we know P implies Q *)
apply f in p.
(* now lets apply g in p to get R *)
apply g in p.
(* now we have R *)
exact p.
Qed.

(* Programmers might just know this as
   function application.
   Coq type checks this function,
   so we know that it is correct.
*)
Definition application (P Q R: Prop)
  (f: P -> Q) (g: Q -> R): P -> R :=
fun p => g (f p).

(*
We can combine the two in the same proof,
because the Curry-Howard Isomorphism says they are the same.
*)
Theorem implication3 (P Q R: Prop): forall
  (f: P -> Q) (g: Q -> R), P -> R.
Proof.
intros f g.
(* This program is a proof *)
exact (fun p =>
  g (f p)
).
Qed.

(*
Underneath all these tactics, they are just code.
When we Print our proofs and code they are all the same:
`g (f p)`
*)
Print implication3.
Print implication1.
Print application.

Theorem implication4 (P Q R: Prop): forall
  (f: P -> Q) (g: Q -> R) (p: P), R.
Proof.
(* Some tactics can do some types of reasoning for us. *)
auto.
(* The proof is irrelevant, we only care that it is true *)
Qed.

(* This is also the same `g (f p)` *)
Print implication4.

(*
Given A and B, we can deduce A

A /\ B
-------
   A
*)
Theorem conjunction (A: Prop) (B: Prop):
  forall
  (pair: A /\ B),
  A.
Proof.
intros pair.
(*
If we squint this looks just like the `product` function below.
This is because logical conjunction is the same as:
products, pairs, tuples or records in programming.
*)
exact (
  match pair with
  | conj A B => A
  end
).
Qed.

(* A * B = (A, B) *)
Definition product (A: Set) (B: Set)
  (pair: A * B): A :=
match pair with
  | (a, b) => a
end.

(*
If we have B then we can deduce A or B.

   B
-------
A \/ B
*)
Theorem disjunction (A: Prop) (B: Prop):
  forall
  (b: B),
  A \/ B.
Proof.
intros.
right.
exact b.
Restart.
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
