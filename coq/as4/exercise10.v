(*Variables A: Set.*)
(*Variables P Q: A -> Prop.*)
(*Variable R : A -> B -> Prop.*)
Theorem exe10 (A: Set)(P Q: A -> Prop):
(forall x: A, (P(x) -> ~Q(x))) -> ~(exists x: A, (P(x) /\ Q(x))).
Proof.
  intros.
  unfold not.
  intros.
  destruct H0.
  destruct H0.
  apply H in H0.
  apply H0.
  apply H1.
Qed.