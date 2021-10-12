Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c. destruct b eqn: Eb.
  - simpl. destruct c eqn: Ec.
    -- reflexivity.
    -- intros. rewrite <- H. reflexivity.
  - simpl. destruct c eqn: Ec.
    -- intros. rewrite <- H. reflexivity.
    -- intros H. reflexivity.
Qed.