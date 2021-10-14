Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros.
  induction H0.
  - apply H.
  - apply le_S. apply IHle.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros.
  induction n as [| n' IH].
  - apply le_n.
  - apply le_S. apply IH.
Qed.
