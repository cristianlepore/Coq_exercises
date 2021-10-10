Theorem In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros.
  split.
  - induction l as [| h t IH].
    + simpl. intros. right. apply H.
    + simpl. intros.
      apply or_assoc.
      destruct H.
      * left. apply H.
      * right. apply IH. apply H.
  - induction l as [| h t IH].
    + simpl. intros. destruct H.
        destruct H.
        apply H.
    + simpl. intros. destruct H. destruct H.
        left. apply H.
        right. apply IH. left. apply H.
        right. apply IH. right. apply H.
Qed.