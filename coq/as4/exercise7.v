(*Variables A: Set.*)
(*Variables P Q: A -> Prop.*)
(*Variable R : A -> B -> Prop.*)
Theorem exe7 (A: Set)(P Q: A -> Prop):
(exists x: A, (~P(x) /\ ~Q(x))) -> (exists x: A, ~(P(x) /\ Q(x))).
Proof.
  intros.
  unfold not.
  destruct H as [a p].
  exists a.
  intros.
  destruct p.
  destruct H.
  destruct H0.
  apply H.
Qed.