From SigmaZK Require Import Base Sigma.

Section ILemmas.
Program Definition lower {n m} : 'I_(n * m) → 'I_n
  := λ x, @Ordinal _ (x %% n)%N _.
Obligation 1.
  move=> [|n] m x.
  - exfalso. rewrite mul0n in x. by destruct x.
  - by apply ltn_pmod.
Qed.

Program Definition upper {n m} : 'I_(n * m) → 'I_m
  := λ x, @Ordinal _ (x %/ n)%N _.
Obligation 1.
  move=> [|n] m x.
  - exfalso. rewrite mul0n in x. by destruct x.
  - by rewrite ltn_divLR // (mulnC m).
Qed.

Program Definition stitch {n m} : 'I_n → 'I_m → 'I_(n * m)
  := λ x y, @Ordinal _ (x + y * n) _.
Obligation 1.
  move=> [|n] m x y; [ by destruct x |].
  rewrite (mulnC n.+1 m) -ltn_divLR // divnDMl //.
  rewrite divn_small // add0n //.
Qed.

Definition stitchK {n m} (x : 'I_(n * m)) : stitch (lower x) (upper x) = x.
Proof. apply ord_inj => /=. by rewrite addnC -divn_eq. Qed.

Definition lowerK {n m} (x : 'I_n) (y : 'I_m) : lower (stitch x y) = x.
Proof.
  apply ord_inj => /=.
  rewrite -modnDm modnMl addn0.
  destruct n; [ by destruct x |]; by rewrite 2!modZp.
Qed.

Definition upperK {n m} (x : 'I_n) (y : 'I_m) : upper (stitch x y) = y.
Proof.
  apply ord_inj => /=.
  destruct n; [ by destruct x |].
  rewrite divnDMl // divn_small //.
Qed.
End ILemmas.


Section Parallel.

Context {Stat Wit Forb : finType} {n m : nat}.
Context {R' : Stat → Wit → Prop} {Err : Forb → Prop}.
Context (L : sigma 'I_n R' Err) (R : sigma 'I_m R' Err).

(* Increases size of challenge space *)
Program Definition Parallel
  : sigma 'I_(n * m) R' Err :=
  {| commit := λ h w '(r1, r2),
       let a1 := L.(commit) h w r1 in
       let a2 := R.(commit) h w r2 in
       (a1, a2)
   ; response := λ h w '(r1, r2) e,
       let z1 := L.(response) h w r1 (lower e) in
       let z2 := R.(response) h w r2 (upper e) in
       (z1, z2)
   ; verify := λ h '(a1, a2) e '(z1, z2),
       L.(verify) h a1 (lower e) z1 && R.(verify) h a2 (upper e) z2
   ; simulate := λ h e '(r1, r2),
       let '(a1, z1) := L.(simulate) h (lower e) r1 in
       let '(a2, z2) := R.(simulate) h (upper e) r2 in
       ((a1, a2), (z1, z2))
   ; extractor := λ h '(a1, a2) e e' '(z1, z2) '(z1', z2'),
       if lower e != lower e' then
         L.(extractor) h a1 (lower e) (lower e') z1 z1'
       else
         R.(extractor) h a2 (upper e) (upper e') z2 z2'
   ; shvzk_fun := λ w e '(r1, r2),
       ( L.(shvzk_fun) w (lower e) r1
       , R.(shvzk_fun) w (upper e) r2
       )
  |}.
Obligation 1.
  move=> h w e [r1 r2] /=.
  pose proof (L.(complete) h w (lower e) r1).
  pose proof (R.(complete) h w (upper e) r2).
  move=> HR /=.
  simpl in H, H0.
  rewrite H // H0 //.
Qed.
Obligation 2.
  move=> h e [r1 r2] /=.
  pose proof (HSl := L.(complete_sim) h (lower e) r1).
  pose proof (HSr := R.(complete_sim) h (upper e) r2).
  destruct L.(simulate), R.(simulate).
  by rewrite HSl HSr.
Qed.
Obligation 3.
  intros w e. apply inv_prod; apply shvzk_inv.
Qed.
Obligation 4.
  move=> h w e [r1 r2] /=.
  pose proof (HSl := L.(shvzk) h w (lower e) r1).
  pose proof (HSr := R.(shvzk) h w (upper e) r2).
  destruct L.(simulate).
  destruct R.(simulate).
  simpl in HSl, HSr |- * => HR.
  destruct (HSl HR), (HSr HR).
  by subst.
Qed.
Obligation 5.
  move=> h [a1 a2] e [z1 z2] e' [z1' z2'] /=.
  move=> /andP [H0 H0'] /andP [H1 H1'] H2.
  destruct (lower e != lower e') eqn:E.
  - apply L.(special_soundness) => //.
  - apply R.(special_soundness) => //.
    move: E => /eqP E.
    apply /eqP => E'.
    rewrite -(stitchK e) E E' stitchK in H2.
    by move: H2 => /eqP.
Qed.

End Parallel.
