Inductive subseq : list nat -> list nat -> Prop :=
| first_case: forall (l2: list nat), subseq [] l2
| second_case: forall (l1 l2: list nat) (x: nat),
    subseq l1 l2  ->
    subseq (x :: l1) (x :: l2)
| third_case: forall (l1 l2: list nat) (x: nat),
    subseq l1 l2 -> subseq l1 (x :: l2).

Theorem subseq_refl : forall (l: list nat),
    subseq l l.
Proof.
  intros.
  induction l as [| h t IH].
  - apply first_case.
  - apply second_case. apply IH.
Qed.

Theorem subseq_app : forall (l1 l2 l3: list nat),
  subseq l1 l2 -> subseq l1 (l2 ++ l3).
Proof.
  intros.
  induction H.
  - apply first_case.
  - simpl. apply second_case. apply IHsubseq.
  - simpl. apply third_case. apply IHsubseq.
Qed.