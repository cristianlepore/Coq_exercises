Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)    reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity.  Qed.

Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n' IHn'].
  - simpl.  reflexivity.
  - simpl. induction m as [| m' IHm'].
    -- rewrite IHn'. reflexivity.
    -- rewrite IHn'. reflexivity.
Qed.

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
(* Incomplete solution for add_assoc
  - induction m.
    -- simpl. rewrite -> add_0_r. reflexivity.
    -- induction p.
      --- rewrite -> add_0_r.
          rewrite -> add_0_r.  
          reflexivity.   
      --- rewrite <- plus_n_Sm.
          rewrite <- plus_n_Sm.
          rewrite <- plus_n_Sm.
          rewrite IHp. reflexivity.
Admitted.
*)