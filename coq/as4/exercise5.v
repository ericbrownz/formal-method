(*Variables A: Set.*)
(*Variables P Q: A -> Prop.*)
(*Variable R : A -> B -> Prop.*)
Theorem exe5 (A: Set)(P Q: A -> Prop):
(forall x: A, (P(x) /\ Q(x))) <-> (forall x: A, P(x)) /\ (forall x: A, Q(x)).
Proof.
  intros.
  split.
  intros.
  split.
  apply H.
  apply H.
  split.
  destruct H.
  apply H.
  destruct H.
  apply H0.
Qed.
