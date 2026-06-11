From SigmaZK Require Import Base Sigma.

Program Definition WitnessMap
  {Stat Wit Wit' Forb Chal : finType}
  {R : Stat → Wit → Prop} {R' : Stat → Wit' → Prop} {Err : Forb → Prop}
  (toW : Wit → Wit') (fromW : Wit' → Wit + Forb)
  (com : ∀ h w, R h w → R' h (toW w))
  (sou : ∀ h w, R' h w → case (R h) Err (fromW w))
  (P : sigma Chal R' Err)
  : sigma Chal R Err :=
  {| commit := λ h w r, P.(commit) h (toW w) r
   ; response := λ h w r e, P.(response) h (toW w) r e
   ; verify := λ h a e z, P.(verify) h a e z
   ; simulate := λ h e r, P.(simulate) h e r
   ; extractor := λ h a e e' z z',
       case fromW inr (P.(extractor) h a e e' z z')
   ; shvzk_fun := λ w e r, P.(shvzk_fun) (toW w) e r
  |}.
Obligation 1.
  intros.
  pose proof P.(complete) h (toW w) e r.
  auto.
Qed.
Obligation 2. intros. apply P.(complete_sim). Qed.
Obligation 3. intros. apply P.(shvzk_inv). Qed.
Obligation 4.
  intros.
  pose proof P.(shvzk) h (toW w) e r.
  destruct P.(simulate) as [a' z'].
  auto.
Qed.
Obligation 5.
  intros.
  pose proof (H' := P.(special_soundness) h a e z e' z').
  destruct P.(extractor); auto.
  by apply sou, H'.
Qed.


(* Variations of WitnessMap *)

Program Definition Iff {H W Forb C : finType}
  {R : H → W → Prop} {R' : H → W → Prop} {Err : Forb → Prop}
  (Hiff : ∀ h w, R h w <-> R' h w)
  (P : sigma C R' Err)
  : sigma C R Err := WitnessMap id inl _ _ P.
Obligation 1. intros. by apply Hiff. Qed.
Obligation 2. intros. by apply Hiff. Qed.

(* WitnessMap with no error term *)
Program Definition WitnessMapNoErr'
  {H W W' C : finType}
  {R : H → W → Prop} {R' : H → W' → Prop}
  (toW : W → W') (fromW : W' → W)
  (com : ∀ h w, R h w → R' h (toW w))
  (sou : ∀ h w, R' h w → R h (fromW w))
  : sigma C R' NoErr → sigma C R NoErr := λ P,
  {| commit := λ h w r, P.(commit) h (toW w) r
   ; response := λ h w r e, P.(response) h (toW w) r e
   ; verify := λ h a e z, P.(verify) h a e z
   ; simulate := λ h e r, P.(simulate) h e r
   ; extractor := λ h a e e' z z',
       case (inl \o fromW) inr (P.(extractor) h a e e' z z')
   ; shvzk_fun := λ w e r, P.(shvzk_fun) (toW w) e r
  |}.
Obligation 1. intros. pose proof P.(complete). auto. Qed.
Obligation 2. intros. apply P.(complete_sim). Qed.
Obligation 3. intros. apply P.(shvzk_inv). Qed.
Obligation 4.
  intros.
  pose proof P.(shvzk) h (toW w) e r.
  destruct P.(simulate) as [a' z'].
  auto.
Qed.
Obligation 5.
  intros.
  pose proof (H' := P.(special_soundness) h a e z e' z').
  destruct P.(extractor); auto.
  by apply sou, H'.
Qed.

Program Definition Map
  {H H' W W' Forb C : finType}
  {R : H → W → Prop} {R' : H' → W' → Prop} {Err : Forb → Prop}
  (toH : H → H') (toW : W → W') (fromW : W' → W + Forb)
  (com : ∀ h w, R h w → R' (toH h) (toW w))
  (sou : ∀ h w, R' (toH h) w → case (R h) Err (fromW w))
  (P : sigma C R' Err) : sigma C R Err :=
  {| commit := λ h w r, P.(commit) (toH h) (toW w) r
   ; response := λ h w r e, P.(response) (toH h) (toW w) r e
   ; verify := λ h a e z, P.(verify) (toH h) a e z
   ; simulate := λ h e r, P.(simulate) (toH h) e r
   ; extractor := λ h a e e' z z',
       case fromW inr (P.(extractor) (toH h) a e e' z z')
   ; shvzk_fun := λ w e r, P.(shvzk_fun) (toW w) e r
  |}.
Obligation 1.
  intros. apply (P.(complete) (toH h) (toW w) e r). auto.
Qed.
Obligation 2. intros. apply P.(complete_sim). Qed.
Obligation 3. intros. apply P.(shvzk_inv). Qed.
Obligation 4.
  intros. pose proof P.(shvzk) (toH h) (toW w) e r.
  destruct P.(simulate) as [a' z']. auto.
Qed.
Obligation 5.
  intros. pose proof P.(special_soundness) (toH h) a e z e' z'.
  destruct P.(extractor); [ by apply sou, H3 | auto ].
Qed.

Program Definition Weaken
  {H W B B' C : finType} 
  {R : H → W → Prop} {E : B → Prop} {E' : B' → Prop}
  (weak : B → B') (sound : ∀ b, E b → E' (weak b))
  (P : sigma C R E) : sigma C R E' :=
  {| commit := λ h w r, P.(commit) h w r
   ; response := λ h w r e, P.(response) h w r e
   ; verify := λ h a e z, P.(verify) h a e z
   ; simulate := λ h e r, P.(simulate) h e r
   ; extractor := λ h a e e' z z',
       case (inl \o id) (inr \o weak) (P.(extractor) h a e e' z z')
   ; shvzk_fun := λ w e r, P.(shvzk_fun) w e r
  |}.
Obligation 1. intros. apply (P.(complete) h w e r). auto. Qed.
Obligation 2. intros. apply P.(complete_sim). Qed.
Obligation 3. intros. apply P.(shvzk_inv). Qed.
Obligation 4.
  intros. pose proof P.(shvzk) h w e r.
  destruct P.(simulate) as [a' z']. auto.
Qed.
Obligation 5.
  intros. pose proof P.(special_soundness) h a e z e' z'.
  destruct P.(extractor) => /=; [ apply H3 => // |].
  by apply sound, H3.
Qed.
