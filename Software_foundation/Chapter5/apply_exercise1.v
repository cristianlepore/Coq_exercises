Theorem rev_exercise1 : forall (l l' : list nat),
  l = rev l' ->
  l' = rev l.
Proof.  
  intros.
  rewrite -> H.
  symmetry. apply rev_involutive.
Qed.