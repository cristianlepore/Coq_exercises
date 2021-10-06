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

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
  | nil, l2' => l2'
  | l1', nil => l1'
  | h1 :: t1, h2 :: t2 => h1 :: h2 :: (alternate t1 t2)
  end.

Example test_alternate1: alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. simpl. reflexivity.  Qed.
Example test_alternate2: alternate [1] [4;5;6] = [1;4;5;6].
Proof. simpl. reflexivity.  Qed.
Example test_alternate3: alternate [1;2;3] [4] = [1;4;2;3].
Proof. simpl. reflexivity.  Qed.
Example test_alternate4: alternate [] [20;30] = [20;30].
Proof. simpl. reflexivity.  Qed.