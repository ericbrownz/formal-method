(*Variables A: Set.*)
(*Variables P Q: A -> Prop.*)
(*Variable R : A -> B -> Prop.*)
Theorem cll2 (A: Set)(P Q: A -> Prop):
forall b: A, P(b) /\ (forall x y: A, (P(x) /\ P(y) -> x = y)) -> (forall x: A,(P(x) <-> x = b)).
Proof.
  intros.
  destruct H.
  split.
  intros.
  apply H0.
  split.
  apply H1.
  apply H.
  intros.
  rewrite H1.
  apply H.
Qed.