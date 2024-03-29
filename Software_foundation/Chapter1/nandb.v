Inductive bool : Type :=
  | true
  | false.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition nandb (b1:bool) (b2:bool) : bool :=
  if (andb b1 b2) then negb (andb b1 b2)
  else true.

Example test_nandb1:               (nandb true false) = true.
  Proof. simpl. reflexivity.  Qed.
Example test_nandb2:               (nandb false false) = true.
  Proof. simpl. reflexivity.  Qed.
Example test_nandb3:               (nandb false true) = true.
  Proof. simpl. reflexivity.  Qed.
Example test_nandb4:               (nandb true true) = false.
  Proof. simpl. reflexivity.  Qed.
