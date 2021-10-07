Definition hd_error (l : natlist) : natoption :=
  match l with
  | nil    => None
  | n :: _ => Some n
  end.

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  intros l default.
  destruct l.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.