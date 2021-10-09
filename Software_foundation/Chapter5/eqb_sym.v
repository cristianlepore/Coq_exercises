Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
  intros n m.
  destruct (n=?m) eqn:eq1.
  - apply eqb_true in eq1. 
    rewrite -> eq1. rewrite eqb_refl. reflexivity. 
  - destruct (m=?n) eqn:eq2.
    -- apply eqb_true in eq2. rewrite -> eq2 in eq1. rewrite eqb_refl in eq1. discriminate eq1.
    -- reflexivity.
Qed.