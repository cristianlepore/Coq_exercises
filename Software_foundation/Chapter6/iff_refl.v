Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  intros P.
  split.
  - intros P1. apply P1.
  - intros P2. apply P2.
Qed.