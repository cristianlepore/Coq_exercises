Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n' IHn'].
  - simpl.  reflexivity.
  - simpl. induction m as [| m' IHm'].
    -- rewrite IHn'. reflexivity.
    -- rewrite IHn'. reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(** Use induction to prove this simple fact about [double]: *)

Lemma double_plus : forall n, double n = n + n .
Proof.
  intros n. induction n.
  - simpl. reflexivity.
  - simpl. rewrite <- plus_n_Sm. rewrite IHn. reflexivity.
Qed.
