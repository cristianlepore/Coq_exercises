Lemma mult_is_O :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H1.  
  destruct n as [| n'].
  - left. reflexivity.
  - destruct m as [| m'].
    + right. reflexivity.
    + inversion H1.
Qed.