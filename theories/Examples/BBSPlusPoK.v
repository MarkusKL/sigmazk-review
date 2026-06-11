From SigmaZK Require Import Base Groups Sigma DepHom Pedersen WitnessMap Common.


Section BBSPlusPoK.
Context (G1 G2 GT : finGroupType) (prime_G1 : prime #|G1|).
Context (order_G2 : #|G2| = #|G1|) (order_GT : #|GT| = #|G1|).
Context (g1 h0 h1 : G1) (g2 : G2) (gen_h1 : generator [set: G1] h1).

Context (e : G1 → G2 → GT).
Context (e_left : ∀ z, Hom (e^~ z)).
Context (e_right : ∀ z, Hom (e z)).

Let prime_GT : prime #|GT|. Proof. by rewrite order_GT. Qed.


Section PairingLemmas.

Lemma e_1_left : ∀ x, e 1 x = 1.
Proof. intros x. by rewrite (Hom1 (e^~ x)). Qed.

Lemma e_1_right : ∀ x, e x 1 = 1.
Proof. intros x. by rewrite (Hom1 (e x)). Qed.

Lemma e_swapn : ∀ x y n, e (x ^+ n) y = e x (y ^+ n).
Proof.
  intros x y n.
  induction n. { by rewrite 2!expg0 e_1_left e_1_right. }
  rewrite 2!expgS e_left e_right. by f_equal.
Qed.

Lemma e_swap : ∀ x y n, e (x ^ n) y = e x (y ^ n%:R).
Proof.
  intros x y n. rewrite /expgr e_swapn. do 2 f_equal.
  by rewrite order_G2 natr_Zp.
Qed.

Lemma e_inv_left : ∀ x y, (e x y)^-1 = e x^-1 y.
Proof. intros x y. by rewrite (Hom_invg (e^~ y)). Qed.

End PairingLemmas.


Let R : G2 → 'Z_#|G1| * G1 * 'Z_#|G1| * 'Z_#|G1| → Prop
    := λ pk '(m, A, e', s), e A (pk * g2 ^ e'%:R) = e (g1 * h0 ^ s * h1 ^ m) g2.

Notation Z1 := 'Z_#|G1|.

#[export] Instance e_left_Hom {G : finGroupType} {F : G → G1} {g}
  : Hom F → Hom (λ x, e (F x) g).
Proof. intros HF x y. by rewrite Hom_mulg e_left. Qed.

Let Err : 'Z_#|G1| → Prop := λ 'e, h1 ^ e = h0.

Lemma expgrV {G : finGroupType} (A : G)
  : right_inverse 1%g -%R (λ x y, A ^ x * A ^ y).
Proof. intros x. by rewrite -expgrD GRing.subrr expgr0. Qed.

Lemma expgrK {G : finGroupType} (g : G)
  : right_loop -%R (λ A x, A * (g ^ x)).
Proof. intros x A. by rewrite -mulgA expgrV mulg1. Qed.

Lemma mulg_inter {G : finGroupType} {x y x' y' : G}
: commute y x' → (x * y) * (x' * y') = (x * x') * (y * y').
Proof. intros HC. by rewrite mulgA -(mulgA _ y) HC !mulgA. Qed.

Program Definition BBSPlusPoK : sigma 'Z_#|G1| R Err :=
  Pedersen_expg h1 (λ '(m, A, e', s), A) gen_h1 prime_G1 (
    Pedersen_expg h1 (λ '(m, A, e', s, r1), h0 ^ r1) gen_h1 prime_G1 (
      WitnessMap
        (R' := λ '(pk, A2, A1) '(m, A, e', s, r1, r2, d1, d2),
          (A1, A2, 1, (e g1 g2)^-1 * e A2 pk) =
            (h0 ^ r1 * h1 ^ r2, A * h1 ^ r1, h0 ^ d1 * h1 ^ d2 * A1 ^ - e',
          e (h0 ^ s * h1 ^ (m + d1) * A2 ^ (- e')) g2 * (e (h1 ^ - r1) pk)^-1
        ))
        (* Note the scope annotation *)
        (λ '(m, A, e', s, r1, r2), (m, A, e', s, r1, r2, r1 * e', r2 * e')%R)
        (λ '(m, A, e', s, r1, r2, d1, d2),
          if (d1 - r1 * e' == 0)%R then
            inl (m, A, e', s, r1, r2)
          else
            inr ((r2 * e' - d2) / (d1 - r1 * e'))%R
        ) _ _ (
        Iff _ (
          DepHomPrime #|G1|
            (G := Z1 * G1 * Z1 * Z1 * Z1 * Z1 * Z1 * Z1)
            (λ '(pk, A2, A1), (A1, A2, 1, (e g1 g2)^-1 * e A2 pk))
            (λ '(pk, A2, A1) '(m, A, e', s, r1, r2, d1, d2),
              (h0 ^ r1 * h1 ^ r2, A * h1 ^ r1, h0 ^ d1 * h1 ^ d2 * A1 ^ - e',
                e (h0 ^ s * h1 ^ (m + d1) * A2 ^ (- e')) g2
                * (e (h1 ^ - r1) pk)^-1)) prime_G1
  )))).
Obligation 1.
  move=> /= [[pk A2] A1] [[[[[m A] e'] s] r1] r2] [[H1 H2] H3].
  apply pair_equal_spec. split.
  1: apply pair_equal_spec; split => //.
  1: apply pair_equal_spec; split => //.
  { rewrite H3 expgrMn // -2!expgrM mulg_inter //.
    by rewrite 2!GRing.mulrN 2!expgrV mulg1. }
  apply mulg_eq_r. rewrite mulgA. apply mulg_eq_l. subst.
  rewrite -e_left expgrK.
  rewrite -e_left expgrMn // -expgrM (mulgC (x := (A ^ _))) !mulgA.
  rewrite e_left -mulgA -expgrD GRing.mulrN GRing.addrK.
  by rewrite -H1 e_right -e_swap -mulgA -e_left expgrV e_1_left mulg1.
Qed.
Obligation 2.
  move=> /= [[pk A2] A1] [[[[[[[m A] e'] s] r1] r2] d1] d2] H /=.
  apply pair_equal_spec in H as [H H4].
  apply pair_equal_spec in H as [H H3].
  apply pair_equal_spec in H as [H1 H2].
  apply mulg_eq_inv_l in H4. 
  rewrite mulgA -e_left in H4.
  apply mulg_eq_inv_r in H4.
  rewrite -e_left in H4.
  destruct (d1 - r1 * e' == 0)%R eqn:H5.
  + rewrite H5 /=. split => //. split => //. subst.
    rewrite expgrK in H4.
    rewrite e_right {}H4 -e_swap (mulgC (x := A)).
    rewrite -e_left -!mulgA 2!(e_left _ g1). f_equal.
    rewrite 2!(e_left _ (h0 ^ s)). f_equal.
    rewrite expgrMn // -mulgA -expgrD GRing.addNr expgr0 mulg1.
    rewrite -expgrM -expgrD -GRing.addrA GRing.mulrN.
    move: H5 => /eqP ->.
    by rewrite GRing.addr0.
  + rewrite H5 /Err /= expgrM.
    symmetry.
    apply expgr_eq_l.
    1: apply Z_is_unit_prime => //; apply /eqP; by rewrite H5.
    apply (mulIg (h1 ^ (d2 - r2 * e'))).
    subst. rewrite expgrMn // -2!expgrM in H3.
    rewrite mulg_inter // -2!expgrD 2!GRing.mulrN in H3.
    rewrite -H3 -(expgr0 h1) -expgrD. f_equal.
    by rewrite GRing.addrA GRing.subrK GRing.subrr.
Qed.
Obligation 3.
  by move=> [[pk A2] A1] [[[[[[[m A] e'] s] r1] r2] d1] d2].
Qed.


(* Camenisch et al *)
Let Rbbs2 : G1 ^ 3 → 'Z_#|G1| ^ 5 → Prop
  := λ '(A', Ab, d) '(m, e', r2, r3, s'),
  Ab * d ^-1 = A' ^ (- e') * h0 ^ r2 ∧ g1 = d ^ r3 * h0 ^ (- s') * h1 ^ m.

Program Definition BBS2 : sigma 'Z_#|G1| Rbbs2 Err :=
  Iff _
    (DepHomPrime _
      (G := Z1 ^ 5)
      (λ '(A', Ab, d), (Ab * d^-1, g1))
      (λ '(A', Ab, d) '(m, e', r2, r3, s'),
        (A' ^ (- e') * h0 ^ r2, d ^ r3 * h0 ^ (- s') * h1 ^ m))
      _).
Obligation 1.
  intros [[A' Ab] d] [[[[m e'] r2] r3] s'].
  apply iff_sym. apply pair_equal_spec.
Qed.

End BBSPlusPoK.
