Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros P.
  unfold not.
  intros H1.
  destruct H1 as [H_left H_right].
  apply H_right in H_left.
  apply H_left.
Qed.