Theorem ev_double : forall n,
  ev (double n).
Proof.
  intros.
  induction n as [| n' IH].
  - simpl. apply ev_0.
  - simpl. apply ev_SS. apply IH.
Qed.