(*Variables A: Set.*)
(*Variables P Q: A -> Prop.*)
(*Variable R : A -> B -> Prop.*)
Theorem exe4 (A: Set)(P Q: A -> Prop):
(forall x: A, (P(x) -> Q(x))) -> (forall x: A, ~Q(x)) -> (forall x: A, ~P(x)).
Proof.
  unfold not.
  intros.
  apply H in H1.
  apply H0 in H1.
  apply H1.
Qed.