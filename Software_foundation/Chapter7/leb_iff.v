Theorem leb_iff : forall n m,
  n <=? m = true <-> n <= m.
Proof.
  intros.
  split.
  - apply leb_complete.
  - apply leb_correct.
Qed.