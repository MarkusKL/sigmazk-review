From SigmaZK Require Import Base Sigma.


Section EQ.

Context {H W Forb : finType} {C : nat}.
Context {R : H → W → Prop} {Err : Forb → Prop}.
Context (P : sigma 'Z_C R Err).

(* EQ construction requires these three properties
   to hold of the underlying protocol P. Basically,
   response, simulator (2nd component) and extractor
   has to be statement and message independent. *)
Context (HEQresp : ∀ h1 h2 w r e,
  P.(response) h1 w r e = P.(response) h2 w r e).
Context (HEQsim : ∀ h1 h2 e r,
  (P.(simulate) h1 e r).2 = (P.(simulate) h2 e r).2).
Context (HEQextr : ∀ h1 h2 a1 a2 e e' z z',
    P.(extractor) h1 a1 e e' z z' = P.(extractor) h2 a2 e e' z z').
(* HEQextr does not hold for RSA based homomorphisms *)
(* extractor depends on (u h). for prime order groups (u h = 1) but for GQ (RSA-group) (u h = h). *)

Program Definition EQ
  : sigma 'Z_C (λ '(h1, h2) w, R h1 w ∧ R h2 w) Err :=
  {| Rand := P.(Rand)
   ; Res := P.(Res)
   ; commit := λ '(h1, h2) w r,
       let a1 := P.(commit) h1 w r in
       let a2 := P.(commit) h2 w r in
       (a1, a2)
   ; response := λ '(h1, h2) w r e,
       P.(response) h1 w r e
   ; verify := λ '(h1, h2) '(a1, a2) e z,
       P.(verify) h1 a1 e z && P.(verify) h2 a2 e z
   ; simulate := λ '(h1, h2) e r,
       let '(a1, z) := P.(simulate) h1 e r in
       let '(a2, z) := P.(simulate) h2 e r in
       ((a1, a2), z)
   ; extractor := λ '(h1, h2) '(a1, a2) e e' z z',
       match P.(extractor) h1 a1 e e' z z' with
       | inl w => inl w
       | inr f => inr f
       end
   ; shvzk_fun := λ w e r, P.(shvzk_fun) w e r
  |}.
Obligation 1.
  move=> [h1 h2] w e r /=.
  pose proof (P.(complete) h1 w e r).
  pose proof (P.(complete) h2 w e r).
  move=> [HRl HRr] /=.
  simpl in H0, H1.
  rewrite H0 // -(HEQresp h2) H1 //.
Qed.
Obligation 2.
  move=> [h1 h2] e r /=.
  pose proof (HSl := P.(complete_sim) h1 e r).
  pose proof (HSr := P.(complete_sim) h2 e r).
  specialize (HEQsim h1 h2 e r).
  destruct P.(simulate), P.(simulate).
  simpl in HEQsim; subst.
  by rewrite HSl HSr.
Qed.
Obligation 3.
  intros w e. apply shvzk_inv.
Qed.
Obligation 4.
  move=> [h1 h2] w e r /=.
  pose proof (HSl := P.(shvzk) h1 w e r).
  pose proof (HSr := P.(shvzk) h2 w e r).
  destruct P.(simulate), P.(simulate).
  simpl in HSl, HSr |- * => [[HRl HRr]].
  destruct (HSl HRl), (HSr HRr).
  by subst.
Qed.
Obligation 5.
  move=> [h1 h2] [a1 a2] e z e' z' /=.
  move=> /andP [H0 H0'] /andP [H1 H1'] H2.
  pose proof (P.(special_soundness) h1 a1 e z e' z').
  pose proof (P.(special_soundness) h2 a2 e z e' z').
  rewrite -(HEQextr h1 _ a1) in H4.
  destruct (P.(extractor)), (P.(extractor)); simpl in *; auto.
Qed.

End EQ.
