Definition plus (n m : cnat) : cnat :=
  fun (X : Type) (f : X -> X) (x: X) => n X f (m X f x).

Example plus_1 : plus zero one = one.
Proof.
  intros. simpl.
  reflexivity.
Qed.

Example plus_2 : plus two three = plus three two.
Proof.
  intros. simpl.
  reflexivity.
Qed.

Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof.
  intros. simpl.
  reflexivity.
Qed.