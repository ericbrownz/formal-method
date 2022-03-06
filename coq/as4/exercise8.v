(*Variables A: Set.*)
(*Variables P Q: A -> Prop.*)
(*Variable R : A -> B -> Prop.*)
Theorem exe8 (A: Set)(P Q: A -> Prop):
(exists x: A, (P(x) \/ Q(x))) <-> (exists x: A, P(x)) \/ (exists x: A, Q(x)).
Proof.
  intros.
  split.
  intros.
  destruct H.
  inversion H.
  left.
  exists x.
  apply H0.
  right.
  exists x.
  apply H0.
  intros.
  destruct H as [H0 | H1].
  inversion H0.
  exists x.
  left.
  apply H.
  inversion H1.
  exists x.
  right.
  apply H.
Qed.