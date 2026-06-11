From SigmaZK Require Import Base Sigma.


Section AND.

Context {Stat Wit Wit' Forb Chal : finType}.
Context {Rl : Stat → Wit → Prop} {Rr : Stat → Wit' → Prop} {Err : Forb → Prop}.
Context (L : sigma Chal Rl Err) (R : sigma Chal Rr Err).

Program Definition AND
  : sigma Chal (λ h '(w1, w2), Rl h w1 ∧ Rr h w2) Err :=
  {| commit := λ h '(w1, w2) '(r1, r2),
       let a1 := L.(commit) h w1 r1 in
       let a2 := R.(commit) h w2 r2 in
       (a1, a2)
   ; response := λ h '(w1, w2) '(r1, r2) e,
       let z1 := L.(response) h w1 r1 e in
       let z2 := R.(response) h w2 r2 e in
       (z1, z2)
   ; verify := λ h '(a1, a2) e '(z1, z2),
       L.(verify) h a1 e z1 && R.(verify) h a2 e z2
   ; simulate := λ h e '(r1, r2),
       let '(a1, z1) := L.(simulate) h e r1 in
       let '(a2, z2) := R.(simulate) h e r2 in
       ((a1, a2), (z1, z2))
   ; extractor := λ h '(a1, a2) e e' '(z1, z2) '(z1', z2'),
       match L.(extractor) h a1 e e' z1 z1'
           , R.(extractor) h a2 e e' z2 z2'
       with
       | inl l, inl r => inl (l, r)
       | inr f, _ => inr f
       | _, inr f => inr f
       end
   ; shvzk_fun := λ '(w1, w2) e '(r1, r2),
       ( L.(shvzk_fun) w1 e r1
       , R.(shvzk_fun) w2 e r2
       )
  |}.
Obligation 1.
  move=> h [w1 w2] e [r1 r2] /=.
  pose proof (L.(complete) h w1 e r1).
  pose proof (R.(complete) h w2 e r2).
  move=> [HRl HRr] /=.
  simpl in H, H0.
  rewrite H // H0 //.
Qed.
Obligation 2.
  move=> h e [r1 r2] /=.
  pose proof (HSl := L.(complete_sim) h e r1).
  pose proof (HSr := R.(complete_sim) h e r2).
  destruct L.(simulate), R.(simulate).
  by rewrite HSl HSr.
Qed.
Obligation 3.
  intros [w1 w2] e. apply inv_prod; apply shvzk_inv.
Qed.
Obligation 4.
  move=> h [w1 w2] e [r1 r2] /=.
  pose proof (HSl := L.(shvzk) h w1 e r1).
  pose proof (HSr := R.(shvzk) h w2 e r2).
  destruct L.(simulate).
  destruct R.(simulate).
  simpl in HSl, HSr |- * => [[HRl HRr]].
  destruct (HSl HRl), (HSr HRr).
  by subst.
Qed.
Obligation 5.
  move=> h [a1 a2] e [z1 z2] e' [z1' z2'] /=.
  move=> /andP [H0 H0'] /andP [H1 H1'] H2.
  pose proof (L.(special_soundness) h a1 e z1 e' z1').
  pose proof (R.(special_soundness) h a2 e z2 e' z2').
  destruct (L.(extractor)), (R.(extractor)); simpl in *; auto.
Qed.

End AND.
