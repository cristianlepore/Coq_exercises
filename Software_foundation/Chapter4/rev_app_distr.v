Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros.
  induction l1 as [| h1 t1 IH1].
  - simpl. rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite -> IH1. rewrite <- app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros.
  induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. rewrite -> rev_app_distr.
    simpl. rewrite -> IH.
    reflexivity.
Qed.