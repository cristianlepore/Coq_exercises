Theorem brack_help : forall n m p: nat,
  n + (m + p) = n + m + p.
Proof.
  intros n m p.
  induction n as [| n'].
    simpl.
    reflexivity.
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Lemma plus_help: forall n m: nat,
  S (n + m) = n + S m.
Proof.
  intros n m.
  induction n as [| n].
    simpl.
    reflexivity.
    simpl.
    rewrite -> IHn.
    reflexivity.
Qed.

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n.
  induction n as [|n'].
    simpl.
    reflexivity.
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n].
    simpl.
    rewrite <- plus_n_O.
    reflexivity.
    simpl.
    rewrite -> IHn.
    rewrite -> plus_help.
    reflexivity.
Qed.

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.  
  intros n m p.
  rewrite -> brack_help.
  assert (H: n + m = m + n).
    rewrite -> plus_comm.
    reflexivity.
  rewrite -> H.
  rewrite <- brack_help.
  reflexivity.
Qed.

Lemma mult_help : forall m n : nat,
  m + (m * n) = m * (S n).
Proof.
  intros m n.
  induction m as [| m'].
    simpl.
    reflexivity.
    simpl.
    rewrite <- IHm'.
    rewrite -> plus_swap.
    reflexivity.
Qed.    

Lemma mult_identity : forall m : nat,
 m * 1 = m.
Proof.
  intros m.
  induction m as [| m'].
    simpl.
    reflexivity.
    simpl.
    rewrite -> IHm'.
    reflexivity.
Qed.

Lemma plus_0_r : forall m : nat,
 m + 0 = m.
Proof.
  intros m.
  induction m as [| m'].
    simpl.
    reflexivity.
    simpl.
    rewrite -> IHm'.
    reflexivity.
Qed.

Theorem mult_comm_helper : forall m n : nat,
  m * S n = m + m * n.
Proof.
  intros m n.
  simpl.
  induction n as [| n'].
    assert (H: m * 0 = 0).
    rewrite -> mult_0_r.
    reflexivity.
    rewrite -> H.
    rewrite -> mult_identity.
    assert (H2: m + 0 = m).
    rewrite -> plus_0_r.
    reflexivity.
    rewrite -> H2.
    reflexivity.
    rewrite -> IHn'.
    assert (H3: m + m * n' = m * S n').
    rewrite -> mult_help.
    reflexivity.
    rewrite -> H3.
    assert (H4: m + m * S n' = m * S (S n')).
    rewrite -> mult_help.
    reflexivity.
    rewrite -> H4.
    reflexivity.
Qed.

Theorem mult_comm : forall m n : nat,
 m * n = n * m.
Proof.
  intros m n.
  induction n as [| n'].
    - simpl. rewrite -> mult_0_r. reflexivity.
    - simpl. rewrite <- IHn'. rewrite -> mult_comm_helper.
    reflexivity.
Qed.