Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y :=
  fold (fun el n => (f el) :: n) l [].

(** Write down a theorem [fold_map_correct] in Coq stating that
   [fold_map] is correct, and prove it.  (Hint: again, remember that
   [reflexivity] simplifies expressions a bit more aggressively than
   [simpl].) *)

Theorem fold_map_correct : forall X Y (l : list X) (f: X -> Y),
  fold_map f l = map f l.
Proof.
  intros.
  induction l.
  - reflexivity.
  - simpl.
    rewrite <- IHl.
    unfold fold_map.
    simpl. reflexivity.
Qed.