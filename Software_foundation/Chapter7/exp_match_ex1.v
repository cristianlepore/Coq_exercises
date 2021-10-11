Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  intros.
  induction ss.
  - simpl.
    apply MStar0.
  - simpl.
    apply MStarApp.
    + apply H.
      simpl. left. reflexivity.
    + simpl.
      apply IHss.
      intros.
      apply H.
      simpl. right. apply H0.
Qed.