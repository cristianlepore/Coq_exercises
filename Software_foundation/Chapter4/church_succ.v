Definition succ (n : cnat) : cnat := 
  fun (X : Type) (f : X -> X) (x: X) => f (n X f x).

Example succ_1 : succ zero = one.
Proof.
  intros. simpl.
  reflexivity.
Qed.

Example succ_2 : succ one = two.
Proof.
  intros. simpl.
  reflexivity.
Qed.

Example succ_3 : succ two = three.
Proof.
  intros. simpl.
  reflexivity.
Qed.