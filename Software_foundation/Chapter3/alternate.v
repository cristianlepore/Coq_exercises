Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
  | nil, l2' => l2'
  | l2', nil => l2'
  | l1', nil => l1'
  | nil, l1' => l1'
  | h1 :: t1, h2 :: t2 => h1 :: h2 :: (alternate t1 t2)
  end.
