Fixpoint even (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => even n'
  end.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity.  Qed.

Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - rewrite -> IHn'. simpl. rewrite -> negb_involutive. reflexivity.
Qed.