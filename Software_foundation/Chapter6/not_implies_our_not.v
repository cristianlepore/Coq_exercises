Fact not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  intros P contra H0 H1.
  destruct contra.
  apply H1.
Qed.