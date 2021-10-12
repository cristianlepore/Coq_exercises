Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.

Proof.
  intros b c. 
  destruct b.
  - simpl. destruct c.
    -- simpl. intros H. reflexivity.
    -- simpl. intros H. rewrite H. reflexivity.
  - simpl. destruct c. 
    -- simpl. intros H. reflexivity.
    -- simpl. intros H. rewrite H. reflexivity.
Qed.