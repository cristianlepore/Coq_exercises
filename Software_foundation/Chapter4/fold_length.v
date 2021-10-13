Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

(* ********************** *)

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
  intros.
  induction l.
  - simpl. reflexivity.
  - simpl. rewrite <- IHl. simpl. reflexivity.
Qed.