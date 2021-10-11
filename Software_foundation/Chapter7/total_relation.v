Inductive total_relation : nat -> nat -> Prop :=
  | tot_rel: forall (n m: nat), total_relation n m.