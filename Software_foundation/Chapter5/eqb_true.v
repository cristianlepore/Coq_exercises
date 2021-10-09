Theorem eqb_true : forall n m,
  n =? m = true -> n = m.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - intros m eq. destruct m as [| m'] eqn:E.
    -- reflexivity.
    -- discriminate eq.
  - intros m eq. destruct m as [| m'] eqn:E.
    -- discriminate eq.
    -- apply f_equal.
    apply IHn'. apply eq.
Qed.