Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros.
  destruct H as [H1 | H2].
  - right. apply H1.
  - left. apply H2.
Qed.