Fixpoint ltb (n m : nat) : bool :=
  match n with
    | O => match m with
             | O    => false
             | S m' => true
           end
    | S n' => match m with
             | O   => false
             | S m'=> ltb n' m'
           end
  end.

Example test_blt_nat1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.