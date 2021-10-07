Theorem leb_refl : forall n:nat,
  (n <=? n) = true.
Proof.
  intros n.
  induction n as [| n'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem zero_neqb_S : forall n:nat,
  0 =? (S n) = false.
Proof.
  intros n.
  simpl. reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros b0.
  induction b0.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem plus_leb_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p.
  intros H.
  induction p.
  - simpl. rewrite H.
  reflexivity.
  - simpl. rewrite IHp.
  reflexivity.
Qed.

Theorem S_neqb_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
  intros n.
  simpl. reflexivity.
Qed.
 
Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  intros n.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite <- add_0_r. simpl. reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
  intros b0 c.
  destruct b0.
  - destruct c.
    -- simpl. reflexivity.
    -- simpl. reflexivity.
  - destruct c.
    -- simpl. reflexivity.
    -- simpl. reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  induction n as [| n'].
  - induction m as [| m'].
    + simpl. reflexivity.
    + simpl. reflexivity.
  - induction m as [| m'].
    + induction p as [| p'].
      * simpl. rewrite IHn'. simpl. reflexivity.
      * simpl. rewrite IHn'. simpl. rewrite add_assoc. reflexivity.
    + induction p as [| p'].
      * simpl. rewrite IHn'. simpl. reflexivity.
      * simpl. rewrite IHn'. simpl. rewrite add_assoc. reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite mult_plus_distr_r. rewrite IHn.
  reflexivity.
Qed.