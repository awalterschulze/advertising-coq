Require Import List.
Import ListNotations.
Require Import Strings.String.

(* GetFreeBook is an inductive predicate that defines a few ways
   that will result in Walter buying you a book.
*)
Inductive GetFreeBook (name: string) (contributors: list string): Prop :=
  | only_contributor:
    contributors = [name]
    -> GetFreeBook name contributors
  | first_contributor:
    (exists
      (rest: list string),
      contributors = name :: rest
    )
    -> GetFreeBook name contributors
  | second_contributor:
    (exists
      (frst: string)
      (rest: list string),
      contributors = frst :: name :: rest
    )
    -> GetFreeBook name contributors
  .

Theorem you_get_a_free_book_if_you_are_the_only_contributor:
  forall (you: string)
         (someone: string)
         (others: list string)
         (contributors: list string),
  contributors = [you] -> GetFreeBook you contributors.
Proof.
intros.
apply only_contributor.
assumption.
Qed.

Theorem you_get_a_free_book_if_you_are_the_first_or_second_contributor:
  forall (you: string)
         (someone: string)
         (others: list string)
         (contributors: list string),
  contributors = you :: others \/
  contributors = someone :: you :: others
  -> GetFreeBook you contributors.
Proof.
intros.
destruct H.
- apply first_contributor.
  exists others.
  assumption.
- apply second_contributor.
  exists someone.
  exists others.
  assumption.
Qed.

Inductive WalterIsOutOfMoney: Prop := .

Inductive MyFalse: Prop := .

Inductive HaveTheBook: Prop :=
  | pdf_is_illegally_downloadable: HaveTheBook
  .

Inductive MyTrue: Prop :=
  | I: MyTrue.

Theorem always_a_way_to_get_the_book:
  WalterIsOutOfMoney -> HaveTheBook.
Proof.
intros WalterIsLying.
induction WalterIsLying.
Qed.

Theorem always_a_way_to_get_the_book_2:
  WalterIsOutOfMoney -> HaveTheBook.
Proof.
intros.
apply pdf_is_illegally_downloadable.
Qed.

Inductive Contains (you: string): list string -> Prop :=
  | head_contributor (others: list string):
    Contains you (you :: others)
  | a_contributor (another: string) (others: list string):
    Contains you others
    -> Contains you (another :: others)
  .

Inductive BonusPoints (you: string) (all_contributors: list string): Prop :=
  | bonus_points:
    Contains you all_contributors ->
    BonusPoints you all_contributors.

Theorem no_bonus_points_for_you:
  forall (you: string)
         (contributors: list string),
         not (Contains you contributors) ->
         not (BonusPoints you contributors).
Proof.
intros.
unfold not.
intros B.
destruct B.
contradiction.
Qed.
