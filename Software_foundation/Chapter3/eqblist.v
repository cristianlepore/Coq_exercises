Module NatList.

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

Theorem beq_nat_refl : forall n : nat,
  true = eq_nat n n.
Admitted.

(**** NEW ****)
Search natlist.

Fixpoint eqblist (l1 l2 : natlist) : bool :=
  match l1, l2 with
    | nil,       nil       => true
    | nil,       _ :: _    => false
    | _ :: _,    nil       => false
    | n1 :: l1', n2 :: l2' => if eqb n1 n2
                              then eqblist l1' l2'
                              else false
    end.

Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l. Admitted.

Example test_eqblist1 :
  (eqblist nil nil = true).
Proof.
  simpl. reflexivity.
Qed.

Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
Proof.
  simpl. reflexivity.
Qed.

Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
Proof.
  simpl. reflexivity.
Qed.

Theorem eq_natlist_refl : forall l:natlist,
  true = eqblist l l.
Proof.
  intros l. induction l as [| n l'].
  - simpl. reflexivity.
  - simpl. rewrite <- beq_nat_refl. rewrite <- IHl'. simpl. reflexivity.
Qed.