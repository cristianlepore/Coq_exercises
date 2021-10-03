Theorem forward_huge : (forall A B C : Prop, A -> (A->B) -> (A->B->C) -> C).

Proof.
  intros A B C.
  intros pA AimpsB AimpsBimpsC.
  pose (pB := AimpsB pA).
  pose (pC := AimpsBimpsC pA pB).
  exact pC.
Show Proof.
Qed.
