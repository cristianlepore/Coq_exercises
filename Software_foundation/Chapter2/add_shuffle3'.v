Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
    intros n m. 
    induction n.
    -- induction m.
      --- simpl. reflexivity.
      --- simpl. rewrite <- IHm. reflexivity.
    -- simpl. induction m.
      --- rewrite IHn. simpl. reflexivity.
      --- simpl. rewrite -> IHn. rewrite -> plus_n_Sm. simpl. reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem add_shuffle3' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite add_assoc.
  rewrite add_assoc. 
  replace (n+m) with (m+n). { reflexivity. }
  - rewrite <- add_comm. reflexivity.
Qed.