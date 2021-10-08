Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X)
                   : list Y := 
  match l with
  | [] => []
  | h :: t => (f h) ++ (flat_map f t)
  end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. 
  simpl.
  reflexivity. 
Qed.