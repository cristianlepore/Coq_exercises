Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

Fixpoint incr (m:bin) : bin :=
  match m with
  | Z => B1 Z
  | B0 n => B1 (n)
  | B1 n => B0 (incr n)
  end.

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z => O
  | B0 n => 2 * (bin_to_nat n)
  | B1 n => 1 + 2 * (bin_to_nat n)
  end.

Theorem incr_bin_to_nat_comm : forall n,
  bin_to_nat (incr n) = S (bin_to_nat n).
Proof.
  intros n.
  induction n as [| n' | n'].
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite IHn'. rewrite plus_n_Sm. reflexivity.
Qed.