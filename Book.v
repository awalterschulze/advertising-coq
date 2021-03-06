Require Import List.
Import ListNotations.
Require Import Strings.String.

(* 
   I will buy you a copy of the book: CoqArt, 
   if you are one of the first two contributing to this repo,
   https://github.com/awalterschulze/regex-reexamined-coq/issues/17
   that makes a pull request that solves a `Good First Issue`.

   GetFreeBook is an inductive predicate that defines a few ways
   that will result in Walter buying you a book.
   GetFreeBook says whether a person with a name is getting a free book,
   based on the list of contributors.
*)
Inductive GetFreeBook (contributors: list string) (you: string): Prop :=
  (* If you are the only contributor, then you get a free book.
     This contributors equals the list that only contains you.
  *)
  | only_contributor:
    contributors = [you]
    -> GetFreeBook contributors you
  (* But you could also be the first contributor,
     in a long list of contributors.
     This is means there exists a list of other contributors
     and you are the first or second in the list.
  *)
  | first_or_second_contributor:
    (exists
      (contributor1: string)
      (contributor2: string)
      (others: list string),
      contributors = contributor1 :: contributor2 :: others /\
      (
         you = contributor1
         \/ you = contributor2
      )
    )
    -> GetFreeBook contributors you
  .
  
(* Now we can prove that if you are the only contributor,
   I will buy you a book.
*)
Theorem you_get_a_free_book_if_you_are_the_only_contributor:
  forall (you: string)
         (contributors: list string),
  contributors = [you] -> GetFreeBook contributors you.
Proof.
intros.
apply only_contributor.
exact H.
Qed.

(* We can also prove that I will buy you a book,
   if you are the first or second contributor
*)
Theorem you_get_a_free_book_if_you_are_the_first_or_second_contributor:
  forall (you: string)
         (someone: string)
         (others: list string)
         (contributors: list string),
  contributors = you :: someone :: others \/
  contributors = someone :: you :: others
  -> GetFreeBook contributors you.
Proof.
intros.
apply first_or_second_contributor.
(* 
With exists we have to provide the possibilities,
but to know if you are the first or second contributor,
we have to destruct the hypothesis H.
*)
destruct H.
- (* Now we know you are the first contributor *)
  exists you.
  exists someone.
  exists others.
  (* This looks provable *)
  auto.
- (* Now it is easy to also proof that case,
     where you are the second contributor. *)
  exists someone.
  exists you.
  exists others.
  auto.
Qed.

(* After buying two contributors a book,
   I will be out of money.
*)

Inductive WalterIsOutOfMoney: Prop := .

(* Doesn't seem like this induction predicate can be constructed.
   It doesn't have any constructors, hmmm.
   Is it possible for Walter to run out of money?
*)

Inductive MyFalse: Prop := .

(* Continuing the Curry-Howard Isomorphism
   This is the Void data type, which has no constructors.
   Doesn't seem like Walter will run out of money,
   but he is trying to passive aggressively say
   that these books aren't cheap and
   he is not buying everyone a book, I am sorry.
*)

(* I wonder if it is possible to have a book anyway *)
Inductive HaveTheBook: Prop :=
  | pdf_is_illegally_downloadable: HaveTheBook
  .

Inductive MyTrue: Prop :=
  | I: MyTrue.
(* Continuing the Curry-Howard Isomorphism
   This is the Unit data type `()`, which represents one value
   that you can always construct out of thin air.
*)

(* Seems it is always possible to get a book *)
Theorem always_a_way_to_get_the_book:
  WalterIsOutOfMoney -> HaveTheBook.
Proof.
intro WalterIsLying.
induction WalterIsLying.
(* If you assume False, you can prove anything *)
Qed.

Theorem always_a_way_to_get_the_book_2:
  HaveTheBook.
Proof.
(* I did not say this *)
apply pdf_is_illegally_downloadable.
Qed.

(* Here is an inductive predicate that is recursively
   defined to say whether a string is in a list.
*)
Inductive Contains (you: string): list string -> Prop :=
  | head_contributor (others: list string):
    Contains you (you :: others)
  | a_contributor (another: string) (others_and_you: list string):
    (* This is the recursive bit *)
    Contains you others_and_you -> Contains you (another :: others_and_you)
  .

Inductive BonusPoints (you: string) (all_contributors: list string): Prop :=
  | bonus_points:
    (* 
       If you contribute not just if you are the first or second contributor.
       You can get bonus points for the functional programming course.
    *)
    Contains you all_contributors ->
    BonusPoints you all_contributors.

(* 
   `not A`
   is the same as
   `A -> False`

   Seems as though if you do not contribute
   you will not get bonus points.
*)
Theorem no_bonus_points_for_you:
  forall (you: string)
         (contributors: list string),
         not (Contains you contributors) ->
         not (BonusPoints you contributors).
Proof.
intros.
unfold not.
(* Now we can see the goal -> False *)
intros B.
destruct B.
(* We have a hypothesis that says:
   you are not a contributor
   and
   you are a contributor
   that is a contradiction
  *)
contradiction.
Qed.

Fixpoint contains (x: string) (xs: list string): bool :=
  match xs with
  | [] => false
  | (x'::xs') =>
    if eqb x x'
    then true
    else contains x xs'
  end.

Theorem contains_correct:
  forall (x: string) (xs: list string),
  contains x xs = true <-> Contains x xs.
Proof.
intros.
split.
- intros.
  induction xs.
  + cbn in H.
    discriminate.
  + cbn in H.
    remember (eqb x a).
    destruct b.
    * Search eqb.
      symmetry in Heqb.
      rewrite eqb_eq in Heqb.
      subst.
      apply head_contributor.
    * apply a_contributor.
      apply IHxs.
      exact H.
- intros.
  induction xs.
  + inversion H.
  + inversion H.
    * cbn.
      rewrite eqb_refl.
      reflexivity.
    * subst.
      cbn.
      apply IHxs in H1.
      rewrite H1.
      remember (eqb x a).
      destruct b; reflexivity.
Qed.

