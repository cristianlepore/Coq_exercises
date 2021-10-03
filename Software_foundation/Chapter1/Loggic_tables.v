Inductive bool : Type :=
  | true
  | false.


Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.


(* Table for NOT *)
Example test_not1: (negb true) = false.
Proof.
  simpl.
  reflexivity.
Qed.
Example test_not2: (negb false) = true.
Proof.
  simpl.
  reflexivity.
Qed.

(* Table for AND *)
Example test_andb1:  (andb true  false) = false.
Proof. simpl. reflexivity.  Qed.
Example test_and2:  (andb false false) = false.
Proof. simpl. reflexivity.  Qed.
Example test_and3:  (andb false true)  = false.
Proof. simpl. reflexivity.  Qed.
Example test_and4:  (andb true  true)  = true.
Proof. simpl. reflexivity.  Qed.


(* Table for OR *)
Example test_orb1:  (orb true  false) = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb2:  (orb false false) = false.
Proof. simpl. reflexivity.  Qed.
Example test_orb3:  (orb false true)  = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb4:  (orb true  true)  = true.
Proof. simpl. reflexivity.  Qed.