(*Variables A: Set.*)
(*Variables P Q: A -> Prop.*)
(*Variable R : A -> B -> Prop.*)
Theorem exe12 (A: Set)(P Q R: A -> Prop):
(exists x: A, (P(x) /\ Q(x))) /\ (forall x: A, (P(x) -> R(x))) -> (exists x: A, (R(x) /\ Q(x))).
Proof.
  intros.
  destruct H.
  destruct H.
  exists x.
  split.
  destruct H.
  apply H0 in H.
  apply H.
  destruct H.
  apply H1.
Qed.