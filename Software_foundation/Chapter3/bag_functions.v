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

(**** NEW ****)

Definition bag := natlist.

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil => O
  | h :: t => match (eq_nat h v) with
              | true => S (count v t)
              | false => count v t
              end
  end.

Example test_count1:              count 1 [1;2;3;1;4;1] = 3.
Proof. simpl. reflexivity. Qed.
Example test_count2:              count 6 [1;2;3;1;4;1] = 0.
Proof. simpl. reflexivity. Qed.

Definition sum : bag -> bag -> bag :=
  app.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.

Definition add (n:nat) (t:bag) : bag :=
  n :: t.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. simpl. reflexivity.  Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. simpl. reflexivity.  Qed.

Definition member (n:nat) (b:bag) : bool :=
  match count n b with
  | O   => false
  | S _ => true
  end.

Example test_member1: member 1 [1;4;1] = true.
Proof. simpl. reflexivity.  Qed.
Example test_member2: member 2 [1;4;1] = false.
Proof. simpl. reflexivity.  Qed.
