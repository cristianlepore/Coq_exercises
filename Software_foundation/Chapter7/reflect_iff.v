Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros.
  destruct b.
  - inversion H.
    split.
    + intros.
      reflexivity.
    + intros.
Abort.