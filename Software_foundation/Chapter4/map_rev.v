Lemma new_lemma : forall (X Y : Type) (f : X -> Y) (l1 l2 : list X),
  map f (l1 ++ l2) = map f l1 ++ (map f l2).
Proof.
  intros.
  induction l1 as [| h1 t1 IH1].
  - reflexivity.
  - simpl. rewrite -> IH1. reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros.
  induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. rewrite -> new_lemma.
    simpl. rewrite -> IH.
    reflexivity.
Qed.