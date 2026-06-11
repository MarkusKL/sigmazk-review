From SigmaZK Require Import Base Sigma.
#[local] Open Scope ring_scope.


Section OR.

Context {Stat Wit Wit' Forb : finType} {n : nat}.
Context {Rl : Stat → Wit → Prop} {Rr : Stat → Wit' → Prop} {Err : Forb → Prop}.
Context (L : sigma 'Z_n Rl Err) (R : sigma 'Z_n Rr Err).

(* Relation Rl h w.2 \/ Rr h w.2 is not strong enough *)
(* Otherwise relation has to be efficiently decidable *)
Program Definition OR
  : sigma 'Z_n (λ h w, case (Rl h) (Rr h) w) Err :=
  {| commit := λ h 'w '(r1, r1', r2, r2', e'), 
       match w with
       | inl w1 =>
         let a1 := L.(commit) h w1 r1 in
         let '(a2, _) := R.(simulate) h e' r2' in
         (a1, a2)
       | inr w2 =>
         let a2 := R.(commit) h w2 r2 in
         let '(a1, _) := L.(simulate) h e' r1' in
         (a1, a2)
       end
   ; response := λ h w '(r1, r1', r2, r2', e') e,
       match w with
       | inl w1 =>
         let e1 := e - e' in
         let '(_, z2) := R.(simulate) h e' r2' in
         let z1 := L.(response) h w1 r1 e1 in
         (e1, z1, e', z2) 
       | inr w2 =>
         let e2 := e - e' in
         let '(_, z1) := L.(simulate) h e' r1' in
         let z2 := R.(response) h w2 r2 e2 in
         (e', z1, e2, z2) 
       end
   ; verify := λ h '(a1, a2) e '(e1, z1, e2, z2),
       (e1 == e - e2)%B
       && L.(verify) h a1 e1 z1
       && R.(verify) h a2 e2 z2
   ; simulate := λ h e '(r1, r1', r2, r2', e'),
       let e1 := e - e' in
       let '(a1, z1) := L.(simulate) h e1 r1' in
       let '(a2, z2) := R.(simulate) h e' r2' in
       ((a1, a2), (e1, z1, e', z2))
   ; extractor := λ h '(a1, a2) e e' '(e1, z1, e2, z2) '(e1', z1', e2', z2'),
       if e1 != e1' then
         match L.(extractor) h a1 e1 e1' z1 z1' with
         | inl l => inl (inl l)
         | inr f => inr f
         end
       else
         match R.(extractor) h a2 e2 e2' z2 z2' with
         | inl r => inl (inr r)
         | inr f => inr f
         end
   ; shvzk_fun := λ w e '(r1, r1', r2, r2', e'),
       match w with
       | inl w1 =>
         ( L.(shvzk_inv) w1 (e - e') r1', L.(shvzk_fun) w1 (e - e') r1
         , r2, r2', e')
       | inr w2 =>
         ( r1, r1'
         , R.(shvzk_inv) w2 (e - e') r2', R.(shvzk_fun) w2 (e - e') r2, e - e')
       end
  |}.
Obligation 1.
  move=> /= h [w1|w2] e [[[[r1 r1'] r2] r2'] e'] /=.
  - pose proof (L.(complete) h w1 (e - e') r1).
    pose proof (R.(complete_sim) h e' r2').
    destruct (R.(simulate)).
    simpl in H0 |- *.
    move=> HRl.
    rewrite eq_refl /= H //= H0.
  - pose proof (R.(complete) h w2 (e - e') r2).
    pose proof (L.(complete_sim) h e' r1').
    destruct (L.(simulate)).
    simpl in H0 |- *.
    move=> HRl.
    by rewrite GRing.subKr eq_refl /= H0 /= H.
Qed.
Obligation 2.
  move=> /= h e [[[[r1 r1'] r2] r2'] e2].
  pose proof (HSl := L.(complete_sim) h (e - e2) r1').
  pose proof (HSr := R.(complete_sim) h e2 r2').
  destruct L.(simulate), R.(simulate).
  by rewrite eq_refl HSl HSr.
Qed.
Obligation 3.
  move=> [w1|w2] e /=.
  - eexists (λ '(r1, r1', r2, r2', e2),
      (L.(shvzk_inv) w1 (e - e2) r1', L.(shvzk_fun) w1 (e - e2) r1, r2, r2', e2)).
    split.
    + intros [[[[r1 r1'] r2] r2'] e2].
      by rewrite 2!(inv_rew (L.(shvzk_inv) w1 (e - e2))).
    + intros [[[[r1 r1'] r2] r2'] e2].
      by rewrite 2!(inv_rew (L.(shvzk_inv) w1 (e - e2))).
  - eexists (λ '(r1, r1', r2, r2', e2),
      (r1, r1', R.(shvzk_inv) w2 e2 r2', R.(shvzk_fun) w2 e2 r2, e - e2)).
    split.
    + intros [[[[r1 r1'] r2] r2'] e2].
      rewrite GRing.subKr.
      by rewrite 2!(inv_rew (R.(shvzk_inv) w2 (e - e2))).
    + intros [[[[r1 r1'] r2] r2'] e2].
      by rewrite GRing.subKr 2!(inv_rew (R.(shvzk_inv) w2 e2)).
Qed.
Obligation 4.
  move=> /= h [w1|w2] e [[[[r1 r1'] r2] r2'] e'] /=.
  - pose proof (HSl := L.(shvzk) h w1 (e - e') r1).
    destruct R.(simulate), L.(simulate).
    simpl in HSl |- * => HRl.
    destruct (HSl HRl).
    by subst.
  - pose proof (HSr := R.(shvzk) h w2 (e - e') r2).
    rewrite GRing.subKr.
    destruct L.(simulate), R.(simulate).
    simpl in HSr |- * => HRr.
    destruct (HSr HRr).
    by subst.
Qed.
Obligation 5.
  move=> /= h [a1 a2] e [[[e1 z1] e2] z2] e' [[[e1' z1'] e2'] z2'].
  move=> /andP [/andP [/eqP ? H0] H0'].
  move=> /andP [/andP [/eqP ? H1] H1'] H2.
  subst.
  destruct (e - e2 != e' - e2') eqn:E; rewrite E /=.
  - pose proof (L.(special_soundness) _ _ _ _ _ _ H0 H1) => //.
    destruct L.(extractor) => //=.
    1,2: rewrite E in H; by apply H.
  - pose proof (R.(special_soundness) _ _ _ _ _ _ H0' H1') => //.
    assert (E' : e2 != e2'). {
      move: E => /eqP E.
      apply /eqP => E'; subst.
      move: H2 => /eqP H2; apply H2.
      by rewrite -(GRing.subrK e2' e) E GRing.subrK.
    }
    rewrite E' in H.
    destruct R.(extractor) => //=.
    1,2: by apply H.
Qed.

End OR.
