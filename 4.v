Theorem backward_large : (forall A B C : Prop, A -> (A->B) -> (B->C) -> C).

Proof.
  intros A B C.
  intros proof_of_A.
  intros A_implies_B.
  pose (proof_of_B := A_implies_B proof_of_A).
  intros B_implies_C.
  pose (proof_of_C := B_implies_C proof_of_B).
  exact proof_of_C.
Qed.
