Definition mult (n m : cnat) : cnat :=
  fun (X : Type) (f : X -> X) => n X (m X f).

Example mult_1 : mult one one = one.
Proof.
  intros. simpl.
  reflexivity.
Qed.

Example mult_2 : mult zero (plus three three) = zero.
Proof.
  intros. simpl.
  reflexivity.
Qed.

Example mult_3 : mult two three = plus three three.
Proof.
  intros. simpl.
  reflexivity.
Qed.