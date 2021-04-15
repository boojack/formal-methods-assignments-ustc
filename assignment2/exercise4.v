Theorem ex4: forall P Q R:Prop,
  (P /\ (Q /\ R)) -> ((P /\ Q) /\ R).
Proof.
intros.
inversion H.
split.
split.
apply H0.
inversion H1.
apply H2.
inversion H1.
apply H3.
Qed.