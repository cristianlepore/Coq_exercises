Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l.
  induction l as [| [x y] l'].
  - intros l1 l2. intros H.
  inversion H.
Abort.
(* incomplete *)