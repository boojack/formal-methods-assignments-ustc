Variables A B: Set.
Variables P Q: A -> Prop.
Variable R : A -> B -> Prop.

Theorem Exercise_3 :
        (forall x: A, (~P x) /\ Q x) -> (forall x: A, P x) -> forall x: A, Q x.
    Proof.
        intros H1 H2 a.
        apply H1.
    Qed.

Theorem Exercise_4 :
        (forall x: A, P x -> Q x) -> (forall x: A, ~Q x) -> forall x: A, ~P x.
    Proof.
        unfold not.
        intros.
        apply H in H1.
        apply H0 in H1.
        apply H1.
    Qed.

Theorem Exercise_5 :
        (forall x: A, P x /\ Q x) <-> (forall x: A, P x) /\ (forall x: A, Q x).
    Proof.
        unfold iff.
        split.
        intros.
        split.
        apply H.
        apply H.
        intros.
        destruct H as [Hp Hq].
        split.
        apply Hp.
        apply Hq.
    Qed.

Theorem Exercise_6 :
        (exists x: A, ~P x \/ Q x) -> (exists x: A, ~(P x /\ ~Q x)).
    Proof.
        unfold not.
        intros.
        destruct H as [a H0].
        exists a.
        inversion H0.
        intros.
        apply H.
        apply H1.
        intros.
        apply H1.
        apply H.
   Qed.

Theorem Exercise_7 :
        (exists x: A, ~P x /\ ~Q x) -> (exists x: A, ~(P x /\ Q x)).
    Proof.
        unfold not.
        intros.
        destruct H as [a H1].
        exists a.
        inversion H1. 
        intros.
        apply H0.
        apply H2.
    Qed.

Theorem Exercise_8 :
        (exists x: A, P x \/ Q x) <-> ((exists x: A, P x) \/ (exists x: A, Q x)).
    Proof.
        unfold iff.
        split.
        intros.
        destruct H as [a H1].
        inversion H1.
        left.
        exists a.
        apply H.
        right.
        exists a.
        apply H.
   
        intros.
        inversion H.
        destruct H0 as [a H1].
        exists a.
        left.
        apply H1.
        destruct H0 as [a H1].
        exists a.
        right.
        apply H1.
    Qed.
