From SigmaZK Require Import Base Groups Sigma.

Section Homomorphism.

Context {Forb : finType} {Err : Forb → Prop}
  {I : finType} {G H : finGroupType}
  (l : nat) (u : I → G)
  (F : I → G → H) (P : I → H)
  (IsHom : ∀ i, Hom (F i))
  (Thm3a : ∀ e e' : 'Z_l, e != e' →
    gcdz l (e%:Z - e'%:Z) = 1%Z)
  (Thm3b : ∀ i, F i (u i) = P i ^+ l).

Notation "x ⊗  y" :=
  (@mulg H x y) (at level 40).

Notation "x ⊕ y" :=
  (@mulg G x y) (at level 40).

Notation "x ^ z" :=
  (expgz x z) : group_scope.

Lemma Hom_expgz {h} {x : G} {z} : F h (x ^ z) = F h x ^ z.
Proof.
  destruct z => /=.
  - rewrite Hom_expgn //.
  - rewrite Hom_invg Hom_expgn //.
Qed.

Program Definition DepHom : sigma 'Z_l (λ h w, P h = F h w) Err :=
  {| commit := λ h w r, F h r
   ; response := λ h w r e, r ⊕ w ^+ e
   ; verify := λ h a e z,
     (F h z == a ⊗ P h ^+ e)%bool
   ; simulate := λ h e r,
       ((F h r ⊗ P h ^- e), r)
   ; extractor := λ h _ e e' z z',
       let (a, b) := egcdz l (e%:Z - e'%:Z) in
       inl (u h ^ a ⊕ (z'^-1 ⊕ z) ^ b)

   ; shvzk_fun := λ w e r, r * w ^+ e
  |}.
Obligation 1.
  move=> h w e r ->.
  by rewrite Hom_mulg Hom_expgn.
Qed.
Obligation 2.
  move=> h e r.
  by rewrite mulgKV.
Qed.
Obligation 3.
  move=> w e.
  exists (mulg^~ (w ^- e)); split;
    intros ?; by rewrite ?mulgK ?mulgKV.
Qed.
Obligation 4.
  split; [| done ].
  move: H0 => ->.
  by rewrite Hom_mulg Hom_expgn mulgK.
Qed.
Obligation 5.
  move=> h a e z e' z' H2 H0 H1.
  case: (@egcdzP l (e%:Z - e'%:Z)) => a' b' E1 E2.
  apply /eqP.
  rewrite Hom_mulg 2!Hom_expgz Hom_mulg Hom_invg.
  move: H2 H0 => /eqP -> /eqP ->.
  rewrite (Thm3b h).
  rewrite invMg mulgA mulgKV.
  rewrite expgz_neg 2!expgz_pos.
  rewrite -expgzM -expgzD -expgzM -expgzD.
  rewrite -{1}(expg1 (P h)) expgz_pos.
  f_equal.
  rewrite -(GRing.addrC e%:Z).
  rewrite (GRing.mulrC) (GRing.mulrC _ b').
  rewrite E1 Thm3a //.
Qed.

End Homomorphism.
