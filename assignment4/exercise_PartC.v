Variables A B: Set.
Variables P Q R: A -> Prop.

Theorem Exercise_9 :
        (exists x: A, ~P x)  -> ~(forall x: A, P x).
    Proof.
        unfold not.
        intros.
        destruct H as [a H1].
        apply H1.
        apply H0.
    Qed.



Theorem Exercise_10 :
        (forall x: A, P x -> ~Q x) -> ~(exists x: A, P x /\ Q x).
    Proof.
        unfold not.
        intros H.
        intros H1.
        destruct H1.
        inversion H0.
        apply H in H1.
        apply H1.
        apply H2.
    Qed.


Theorem Exercise_11 :
        ((forall x: A, P x -> Q x) /\ (exists x:A, P x)) -> (exists x: A, Q x).
    Proof.
        intros.
        destruct H as [H1 H2].
        destruct H2 as [a H3].
        exists a.
        apply H1.
        apply H3.
    Qed.

Theorem Exercise_12 :
        (exists x: A, P x /\ Q x) /\ (forall x:A, P x -> R x) -> (exists x: A, R x /\ Q x).
    Proof.
        intros.
        destruct H as [H1 H2].
        destruct H1 as [a H3].
        exists a.
        inversion H3.
        split.
        apply H2.
        apply H.
        apply H0.
    Qed.

