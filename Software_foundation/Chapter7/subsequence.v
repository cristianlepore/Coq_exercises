Inductive subseq : list nat -> list nat -> Prop :=
| nil_is_subseq: forall (l2: list nat), subseq [] l2
| combine_subseq: forall (l1 l2: list nat) (x: nat),
    subseq l1 l2  ->
    subseq (x :: l1) (x :: l2)
| subseq_larger: forall (l1 l2: list nat) (x: nat),
    subseq l1 l2 -> subseq l1 (x :: l2).

Theorem subseq_refl : forall (l: list nat),
    subseq l l.
Proof.
  intros.
  induction l as [| h t IH].
  - apply nil_is_subseq.
  - apply combine_subseq. apply IH.
Qed.

Theorem subseq_app : forall (l1 l2 l3: list nat),
  subseq l1 l2 -> subseq l1 (l2 ++ l3).
Proof.
  intros.
  induction H.
  - apply nil_is_subseq.
  - simpl. apply combine_subseq. apply IHsubseq.
  - simpl. apply subseq_larger. apply IHsubseq.
Qed.

Theorem subseq_trans :  forall (l1 l2 l3: list nat),
  subseq l1 l2 /\ subseq l2 l3 -> subseq l1 l3.
Proof.
  intros.
  destruct H.
  generalize dependent H.
  generalize dependent l1.
  induction H0.
  - intros.
    inversion H.
    apply nil_is_subseq.
  - intros.
    inversion H.
    + apply nil_is_subseq.
    + apply combine_subseq.
      apply IHsubseq.
      apply H3.
    + apply subseq_larger.
      apply IHsubseq.
      apply H3.
  - intros.
    apply subseq_larger.
    apply IHsubseq.
    apply H.
Qed.