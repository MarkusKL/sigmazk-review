From SigmaZK Require Import Base Sigma.

Program Definition Pedersen
  {Stat Wit Forb Chal G G' : finType}
  {R : Stat → Wit → Prop} {Err : Forb → Prop}
  (f : Wit → G → G') (Hf : ∀ w, inverse (f w))
  (P : sigma Chal (λ '(h, B) '(w, r), R h w ∧ B = f w r) Err)
  : sigma Chal R Err :=
  {| commit := λ h w r,
       let B := f w r.2 in
       let a := P.(commit) (h, B) (w, r.2) r.1 in
       (a, B)
   ; response := λ h w r e,
       let B := f w r.2 in
       P.(response) (h, B) (w, r.2) r.1 e
   ; verify := λ h '(a, B) e z,
       P.(verify) (h, B) a e z
   ; simulate := λ h e r,
       let '(a, z) := P.(simulate) (h, r.2) e r.1 in
       ((a, r.2), z)
   ; extractor := λ h '(a, B) e e' z z',
       case (inl \o fst) inr (P.(extractor) (h, B) a e e' z z')
   ; shvzk_fun := λ w e '(r, r'),
       (P.(shvzk_fun) (w, r') e r, f w r')
  |}.
Obligation 1.
  move=> H W C Forb G G' R Err f Hf P.
  move=> h w e [r r'] /=.
  pose proof (HP := P.(complete) (h, f w r') (w, r') e r).
  intros HR. by apply HP.
Qed.
Obligation 2.
  move=> H W C Forb G G' R Err f Hf P.
  move=> h e [r r'].
  pose proof (HP := P.(complete_sim) (h, r') e r).
  by destruct P.(simulate).
Qed.
Obligation 3.
  move=> H W C Forb G G' R Err f Hf P.
  move=> w e.
  apply inv_dep => //.
  move=> g. apply P.(shvzk_inv).
Qed.
Obligation 4.
  move=> H W C Forb G G' R Err f Hf P.
  move=> h w e [r r'] /=.
  pose proof (HP := P.(shvzk) (h, f w r') (w, r') e r).
  destruct P.(simulate) as [a' z'] => /= HR.
  specialize (HP (conj HR erefl)).
  destruct HP; by subst.
Qed.
Obligation 5.
  move=> H W C Forb G G' R Err f Hf P.
  move=> h [a r] e z e' z' Hez Hez' Hee'.
  pose proof (HP := P.(special_soundness) _ _ _ _ _ _ Hez Hez' Hee').
  destruct P.(extractor) as [[? ?]|] => //; simpl in HP |- *.
  by destruct HP.
Qed.
