 Theorem Exercise_1: forall P Q: Prop,
        ~(P \/ Q) -> ~P /\ ~Q.
    Proof.
        unfold not.
        intros.
        split.
        intros.
        apply H.
        left.
        apply H0.  
        intros.
        apply H.
        right.
        apply H0.
    Qed.

Theorem Exercise_2: forall P Q R: Prop,
        P /\ (Q \/ R) <-> (P /\ Q) \/ (P /\ R).
    Proof.
        intros.
        split.
        intros.
        inversion H.
        inversion H1.
        left.
        split.
        apply H0.
        apply H2.
        right.
        split.
        apply H0.
        apply H2.
        
        intros.
        inversion H.
        inversion H0.
        split.
        apply H1.
        left.
        apply H2.
        split.
        inversion H0.
        apply H1.
        inversion H0.
        right.
        apply H2.
    Qed.