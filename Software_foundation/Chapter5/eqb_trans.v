Theorem eqb_trans : forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof.
  intros  n m p H1 H2.
  apply eqb_true in H1.
  apply eqb_true in H2.
  rewrite -> H2 in H1.
  rewrite -> H1.
  rewrite eqb_refl.
  reflexivity.
Qed.