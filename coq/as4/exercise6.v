(*Variables A: Set.*)
(*Variables P Q: A -> Prop.*)
(*Variable R : A -> B -> Prop.*)
Theorem exe6 (A: Set)(P Q: A -> Prop):
(exists x: A, (~P(x) \/ Q(x))) -> (exists x: A, ~(P(x) /\ ~Q(x))).
Proof.
  intros.
  unfold not.
  destruct H as [a p].
  exists a.
  intros.
  destruct p.
  destruct H0.
  destruct H.
  apply H.
  destruct H.
  apply H1.
  apply H0.
Qed.