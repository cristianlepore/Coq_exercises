Inductive nostutter {X:Type} : list X -> Prop :=
| nostutter_nil: nostutter []
| nostutter_cons: forall (x:X), nostutter (x :: [])
| nostutter_xy: forall (x y: X) (l: list X),
    x <> y -> nostutter (y :: l) -> nostutter (x :: y :: l).

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof.
Abort.

Example test_nostutter_2: nostutter (@nil nat).
Proof.
  repeat constructor.
Qed.

Example test_nostutter_3: nostutter [5].
Proof.
  repeat constructor.
Qed.

Example test_nostutter_4: not (nostutter [3;1;1;4]).
  Proof. intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  contradiction H1; auto.
Qed.