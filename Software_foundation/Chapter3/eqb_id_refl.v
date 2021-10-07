Theorem eqb_id_refl : forall x, eqb_id x x = true.
Proof.
  intros x.
  destruct x.
  - simpl. rewrite eqb_refl. reflexivity.
Qed.
