Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros.
  destruct b eqn:Eb.
  - rewrite H. rewrite H. reflexivity.
  - rewrite H. rewrite H. reflexivity.
Qed.