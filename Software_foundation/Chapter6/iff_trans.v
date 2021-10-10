Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros.
  destruct H as [Hpq Hqp].
  destruct H0 as [Hqr Hrq].
  split.
  - intros.
    apply Hqr.
    apply Hpq.
    apply H.
  - intros.
    apply Hqp.
    apply Hrq.
    apply H.
Qed.