From SigmaZK Require Import Base Sigma.


Section Shrink.
(* Shrink the challenge space of a protocol. *)

Context {Stat Wit Forb : finType} {n m : nat}.
Context {R : Stat → Wit → Prop} {Err : Forb → Prop}.
Context (leqC : (m <= n)%N).
Context (P : sigma 'I_n R Err).

Definition coerce : 'I_m → 'I_n
  := λ x, cast_ord (subnK leqC) (rshift (n - m) x).

Lemma coerce_inj : injective coerce.
Proof. apply (inj_comp (@cast_ord_inj _ _ _)), rshift_inj. Qed.


Program Definition Shrink
  : sigma 'I_m R Err :=
  {| commit := P.(commit)
   ; response := λ h w s e,
       P.(response) h w s (coerce e)
   ; verify := λ h a e z,
       P.(verify) h a (coerce e) z
   ; simulate := λ h e r, P.(simulate) h (coerce e) r
   ; extractor := λ h a e e' z z',
       P.(extractor) h a (coerce e) (coerce e') z z'
   ; shvzk_fun := λ w e r,
       P.(shvzk_fun) w (coerce e) r
  |}.
Obligation 1.
  move=> h w e r /=.
  pose proof (P.(complete) h w (coerce e) r).
  move=> HR /=.
  rewrite H //.
Qed.
Obligation 2.
  move=> h e r /=.
  pose proof (HS := P.(complete_sim) h (coerce e) r).
  destruct P.(simulate).
  by rewrite HS.
Qed.
Obligation 3.
  intros w e. apply shvzk_inv.
Qed.
Obligation 4.
  move=> h w e r /=.
  pose proof (HS := P.(shvzk) h w (coerce e) r).
  destruct P.(simulate).
  simpl in HS |- * => HR.
  by destruct (HS HR).
Qed.
Obligation 5.
  move=> h a e z e' z' /= H0 H1 /eqP H2.
  apply P.(special_soundness) => //.
  apply /eqP => E.
  by apply coerce_inj in E.
Qed.

End Shrink.
