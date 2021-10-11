Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros.
  induction H.
  - apply H0.
  - simpl.
    apply ev_SS.
    apply IHev.
Qed.