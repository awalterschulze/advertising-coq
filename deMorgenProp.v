Lemma deMorgen: forall x y:Prop, not (x \/ y) <-> not x /\ not y.
Proof.
intros.
unfold not.
split.
- intros.
  split.
  + intros.
    apply H.
    left.
    exact H0.
  + intros.
    apply H.
    right.
    assumption.
- intros.
  destruct H.
  destruct H0.
  + apply H.
    assumption.
  + apply H1.
    assumption. 
Qed.

