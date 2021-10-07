Module NatList.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Definition bag := natlist.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Fixpoint eq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
	  | O => true
  	| S m' => false
	  end
    | S n' => match m with
	    | O => false
	    | S m' => eq_nat n' m'
	    end
  end.

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil => O
  | h :: t => match (eq_nat h v) with
              | true => S (count v t)
              | false => count v t
              end
  end.

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  (* When remove_one is applied to a bag without the number to remove,
     it should return the same bag unchanged. *)
  match s with
  | nil => nil
  | h :: t => match eq_nat h v with
              | true => t
              | false => h :: (remove_one v t)
              end
  end.

Theorem ble_n_Sn : forall n,
  ble_nat n (S n) = true.
Proof.
  intro n.
  induction n as [| n'].
  reflexivity.
  simpl.
  rewrite IHn'.
  reflexivity.
Qed.

(**** NEW ****)

Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  intros s.
  induction s.
  - simpl. reflexivity.
  - simpl. destruct n.
    -- simpl. rewrite ble_n_Sn. reflexivity.
    -- simpl. rewrite IHs. reflexivity.
  Qed.
