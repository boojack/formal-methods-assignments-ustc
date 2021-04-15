Theorem ex7: forall P Q R:Prop,
  (P -> Q /\ R) -> ((P -> Q) /\ (P -> R)).
Proof.
intros.
split.
intro.
destruct H as [H1 H2].
apply H0.
apply H1.
intro.
destruct H.
apply H0.
apply H1.
Qed.