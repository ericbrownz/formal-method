Theorem challenge1: forall P Q R: Prop,
    (P /\ Q -> R) <-> (P -> Q -> R).
Proof.
    intros.
    split.
    intros.
    apply H.
    split.
    apply H0.
    apply H1.
    intros.
    inversion H0.
    apply H in H2.
    apply H2.
    apply H1.
Qed.