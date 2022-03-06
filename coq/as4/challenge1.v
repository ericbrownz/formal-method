(*Variables A: Set.*)
(*Variables P Q: A -> Prop.*)
(*Variable R : A -> B -> Prop.*)
Theorem cll1 (A: Set)(P Q: A * A -> Prop):
(exists x: A, exists y: A, P(x,y)) -> (exists y: A, exists x: A, P(x,y)).
Proof.
  intros.
  destruct H.
  destruct H.
  exists x0.
  exists x.
  apply H.
Qed.