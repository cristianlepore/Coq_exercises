Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c. destruct b eqn: Eb.
  - simpl. destruct c eqn: Ec.
    -- reflexivity.
    -- rewrite <- Ec. rewrite <- Eb. intros H. rewrite <- H. reflexivity.
  - simpl. destruct c eqn: Ec.
    -- rewrite <- Ec. rewrite <- Eb. intros H. rewrite <- H. reflexivity.
    -- intros H. reflexivity.
Qed.