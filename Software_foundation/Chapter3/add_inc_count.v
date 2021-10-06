Module NatList.

Inductive natprod : Type :=
  | pair (n1 n2 : nat).

Notation "( x , y )" := (pair x y).

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | cons O t => nonzeros t
  | cons h t => cons h (nonzeros t)
  end.

Fixpoint evenum (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenum n'
  end.

Definition oddnum (n:nat) : bool   :=   negb (evenum n).

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

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

Definition bag := natlist.

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil => O
  | h :: t => match (eq_nat h v) with
              | true => S (count v t)
              | false => count v t
              end
  end.

Definition add (n:nat) (t:bag) : bag :=
  n :: t.

Theorem eq_nat_refl : forall n : nat,
  true = eq_nat n n.
Proof.
  intros n. induction n.
  - simpl. reflexivity.
  - rewrite -> IHn. simpl. reflexivity.
Qed.

(**** NEW ****)

(*  Adding a value to a bag should increase the value's count by one. *)

Theorem add_count: forall (n : nat) (s : bag),
  count n (add n s) = S (count n s).
Proof.
  intros n s.
  destruct s as [| l].
  - simpl. rewrite <- eq_nat_refl.
  reflexivity.
  - simpl. rewrite <- eq_nat_refl. reflexivity.
Qed.
