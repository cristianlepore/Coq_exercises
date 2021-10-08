Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof.
  intros.
  injection H as H1 H2.
  assert (H': z::l = y::l). { rewrite H2. symmetry. apply H0. }
  - injection H' as H4.
    rewrite H1. apply H4.
Qed.