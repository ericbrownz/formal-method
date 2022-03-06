(*Variables A: Set.*)
(*Variables P Q: A -> Prop.*)
(*Variable R : A -> B -> Prop.*)
Theorem exe9 (A: Set)(P Q: A -> Prop):
(exists x: A, ~P(x)) -> ~(forall x: A, P(x)).
Proof.
  intros.
  unfold not.
  destruct H.
  intros.
  destruct H.
  apply H0.
Qed.