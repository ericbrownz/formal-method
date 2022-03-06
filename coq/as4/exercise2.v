Theorem exercise2 : forall P Q R: Prop,
  P /\ (Q \/ R) <-> (P /\ Q) \/ (P /\ R).
Proof.
  intros.
  split.
  intros.
  inversion H.
  destruct H1.
  left.
  split.
  apply H0.
  apply H1.
  right.
  split.
  apply H0.
  apply H1.
  intros.
  split.
  destruct H as [Hl | Hr].
  inversion Hl.
  apply H.
  inversion Hr.
  apply H.
  destruct H as [Hl | Hr].
  left.
  inversion Hl.
  apply H0.
  inversion Hr.
  right.
  apply H0.
Qed.