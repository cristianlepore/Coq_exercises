Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m O.
  intros n_eq_m m_eq_O.
  rewrite -> n_eq_m.
  rewrite <- m_eq_O.
  reflexivity.
Qed.