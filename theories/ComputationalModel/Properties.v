From SigmaZK Require Import Base Scheme Sigma.

From extructures Require Import ord fset fmap.
From mathcomp Require Import reals distr realsum.

From SSProve.Crypt Require Import NominalPrelude.
Import PackageNotation.
#[local] Open Scope package_scope.


Section Properties.

Context {H W F C : finType} {R : H → W → Prop}.
Context {E : F → Prop} (P : sigma C R E).
Import Sigma.

Program Definition sigma_as_scheme : Scheme.sigma :=
  {| Scheme.Stmt := 'fin #|H|
   ; Scheme.Wit := 'fin #|W|
   ; Scheme.Mes := 'fin #|P.(Mes)|
   ; Scheme.State := 'fin #|P.(Rand)|
   ; Scheme.Chal := 'fin #|C|
   ; Scheme.Res := 'fin #|P.(Res)|

   ; Scheme.R := λ h w, boolp.asbool (R (otf h) (otf w))
   ; Scheme.commit := λ h w, {code
       r ← sample uniform #|P.(Rand)| ;;
       let a := P.(commit) (otf h) (otf w) (otf r) in
       ret (fto a, r)
     }
   ; Scheme.response := λ h w _ s e, {code
       ret (fto (P.(response) (otf h) (otf w) (otf s) (otf e)))
     }
   ; Scheme.verify := λ h a e z,
       P.(verify) (otf h) (otf a) (otf e) (otf z)
   ; Scheme.simulate := λ h e, {code
       r ← sample uniform #|P.(RandSim)| ;;
       let '(a, z) := P.(simulate) (otf h) (otf e) (otf r) in
       ret (fto a, fto z)
     }
   ; Scheme.extractor := λ h w e e' z z',
       match P.(extractor) (otf h) (otf w) (otf e) (otf e') (otf z) (otf z') with
       | inl w => Some (fto w)
       | inr f => None
       end
  |}.

Let P' := sigma_as_scheme.

Theorem sigma_Complete A
  `{LtRand : Lt 0 #|Rand P|}
  `{VA : ValidPackage (loc A) (IComplete P') A_export A} :
  AdvOf (Complete P') A = 0%R.
Proof.
  eapply prove_perfect; [| eassumption ].
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel hwe.
  destruct hwe as [[h w] e].
  ssprove_sync => /boolp.asboolP HR.
  apply r_const_sample_L => [|r].
  1: apply LosslessOp_uniform; exact _.
  pose proof (Hcom := complete P (otf h) (otf w) (otf e) (otf r)).
  apply r_ret => s0 s1 H'.
  split; [ | assumption ].
  rewrite !otf_fto Hcom //.
Qed.

Lemma fto_shvzk_bij w e : bijective (fto \o P.(shvzk_fun) w e \o otf).
Proof.
  eapply bij_comp.
  - eapply bij_comp.
    + exists otf; intros ?; rewrite ?otf_fto ?fto_otf //. 
    + destruct (P.(shvzk_inv) w e) as [inv H'].
      exists inv; apply H'.
  - exists fto; intros ?; rewrite ?otf_fto ?fto_otf //. 
Qed.

Theorem sigma_SHVZK A
  `{ValidPackage (loc A) (ITranscript P') A_export A} :
  AdvOf (SHVZK P') A = 0%R.
Proof. (* only relies on group homomorphism *)
  eapply prove_perfect; [| eassumption ].
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel hwe.
  destruct hwe as [[h w] e].
  rewrite -(fto_otf h) -(fto_otf e).
  move: (otf w) (otf h) (otf e) => {}w {}h {}e.
  rewrite otf_fto.
  ssprove_sync_eq => /boolp.asboolP HR.

  eapply r_uniform_bij with (1 := fto_shvzk_bij w e) => r.

  pose proof (HS := shvzk P h w e (otf r)).
  rewrite 2!otf_fto /=.
  destruct (simulate P).
  simpl in HS |- *.
  destruct (HS HR).

  apply r_ret.
  intros s₀ s₁ Hs.
  split; [| assumption ].
  by do 2 f_equal.
Qed.

Definition GUESS := 40%N.

Definition IRel (A : finType) :=
  [interface [ GUESS ] : { 'fin #|A| ~> bool } ].

Definition Rel {A : finType}
  (R : A → Prop) b : game (IRel A) :=
  [package emptym ;
    [ GUESS ] : { 'fin #|A| ~> bool } (w) {
      ret (b && boolp.asbool (R (otf w)))
    }
  ].

Theorem Rel_NoErr
  A `{ValidPackage (loc A) (IRel void) A_export A} :
  AdvOf (Rel NoErr) A = 0%R.
Proof.
  eapply prove_perfect; [| eassumption ].
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel h.
  apply r_ret => s0 s1 H'. split; [| assumption ].
  by apply /boolp.asboolP.
Qed.


Definition SSRed : package (IRel F) (ISoundness P') :=
  [package emptym ;
    [ SOUNDNESS ] '(h, a, (e, z), (e', z')) {
      let v1 := P'.(Scheme.verify) h a e z in
      let v2 := P'.(Scheme.verify) h a e' z' in
      let v3 := e != e' in
      match P.(extractor) (otf h) (otf a) (otf e) (otf e') (otf z) (otf z') with
      | inl w => 
          ret [==> v1, v2, v3 =>
            P'.(Scheme.R) h (fto w)
          ]
      | inr f =>
          b ← call [ GUESS ] : { 'fin #|F| ~> bool} (fto f) ;;
          ret [==> v1, v2, v3, b => false]
      end
    }
  ].

Lemma SSRed_perfect b :
  perfect (ISoundness P') (Special_Soundness P' b) (SSRed ∘ Rel E b).
Proof.
  ssprove_share. eapply prove_perfect.
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel h.
  destruct h as [[[h a] [e1 z1]] [e2 z2]].
  ssprove_code_simpl.
  pose proof (P.(special_soundness) (otf h) (otf a) (otf e1) (otf z1) (otf e2) (otf z2)).
  destruct (P.(extractor)) => /=.
  - apply r_ret => s0 s1 H'.
    split; [| assumption ].

    apply implyb_id2l => H1.
    apply implyb_id2l => H2.
    apply implyb_id2l => H3.
    apply implyb_idl => _.
    apply /boolp.asboolP.
    rewrite otf_fto. apply H0 => //.
    rewrite -(fto_otf e1) in H3.
    apply /eqP => H4.
    rewrite H4 fto_otf eq_refl // in H3.
  - apply r_ret => s0 s1 H'.
    split; [| assumption ].
    apply implyb_id2l => H1.
    apply implyb_id2l => H2.
    apply implyb_id2l => H3.
    rewrite 2!implybF.
    f_equal. destruct b => //=.
    symmetry.
    apply /boolp.asboolP.
    rewrite otf_fto. apply H0 => //.
    rewrite -(fto_otf e1) in H3.
    apply /eqP => H4.
    rewrite H4 fto_otf eq_refl // in H3.
Qed.

Theorem sigma_Special_Soundness A
  `{ValidPackage (loc A) (ISoundness P') A_export A} :
  AdvOf (Special_Soundness P') A = AdvOf (Rel E) (A ∘ SSRed)%sep.
Proof. by rewrite (AdvOf_perfect SSRed_perfect) Adv_reduction. Qed.

End Properties.
