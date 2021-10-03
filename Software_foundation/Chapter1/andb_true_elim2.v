Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.

Proof.
  intros b c. 
  destruct c eqn:Ec.
  - intros H1. reflexivity.
  - destruct b eqn:Eb.
    -- simpl. intros H. rewrite H. reflexivity.
    -- simpl. intros H. rewrite H. reflexivity.
Qed.