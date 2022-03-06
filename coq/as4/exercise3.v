(*Variables A: Set.*)
(*Variables P Q: A -> Prop.*)
(*Variable R : A -> B -> Prop.*)
Theorem exe3 (A: Set)(P Q: A -> Prop):
(forall x: A, (~P(x) /\ Q(x))) -> (forall x: A, (P(x) -> Q(x))).
Proof.
  unfold not.
  intros.
  apply H.
Qed.