Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H1 contra.
  unfold not.
  unfold not in contra.
  intros HP.
  apply contra in H1. 
  apply H1.
  apply HP.
Qed.