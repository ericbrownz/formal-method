Theorem challenge2: forall P Q: Prop,
    (P -> Q) -> (~Q -> ~P).
Proof.
    intros.
    unfold not.
    intros.
    unfold not in H0.
    apply H in H1.
    apply H0 in H1.
    apply H1.
Qed.

Theorem challenge2': forall P Q: Prop,
    (P -> Q) -> (~Q -> ~P).
Proof.
    intros.
    unfold not.
    intros.
    unfold not in H0.
    apply H0 in H.
    apply H.
    apply H1.
Qed.