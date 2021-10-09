Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H1.
  split.
  - destruct n as [| n'].
    -- reflexivity.
    -- inversion H1.
  - destruct m as [| m'].
    -- reflexivity.
    -- rewrite -> add_comm in H1.
       inversion H1.
Qed.
