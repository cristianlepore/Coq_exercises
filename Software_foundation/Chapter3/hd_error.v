Definition hd_opt (l : natlist) : natoption :=
  match l with
  | nil    => None
  | n :: _ => Some n
  end.