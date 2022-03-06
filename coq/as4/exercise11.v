(*Variables A: Set.*)
(*Variables P Q: A -> Prop.*)
(*Variable R : A -> B -> Prop.*)
Theorem exe11 (A: Set)(P Q: A -> Prop):
(forall x: A, (P(x) -> Q(x))) /\ (exists x: A, P(x)) -> (exists x: A, Q(x)).
Proof.
  intros.
  destruct H.
  destruct H0.
  exists x.
  apply H in H0.
  apply H0.
Qed.