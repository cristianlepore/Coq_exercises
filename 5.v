Theorem backward_large : (forall A B C : Prop, A -> (A->B) -> (B->C) -> C).

Proof.
  intros A B C.
  intros proof_of_A.
  intros A_implies_B.
  intros B_implies_C.
  refine (B_implies_C _).
    refine (A_implies_B _).
      exact proof_of_A.
Qed.
