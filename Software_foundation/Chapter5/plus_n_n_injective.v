Theorem plus_n_n_injective : forall n m,
  n + n = m + m ->
  n = m.
Proof.
  intros n. induction n as [| n'].
  - destruct m. 
    -- intro H. reflexivity.
    -- simpl. intro H2. inversion H2.
  - destruct m as [|m'].
    -- intros H2. inversion H2.
    -- intro H. Search (S _ = S _). apply eq_S.
    apply IHn'. simpl in H. inversion H.
    rewrite <- plus_n_Sm in H1. 
    rewrite <- plus_n_Sm in H1. 
    inversion H1. reflexivity.
Qed.