From SigmaZK Require Import Base Groups Sigma DepHom WitnessMap Common.

Section Inverse.
Context (G : finGroupType).
Context (prime_G : prime #|G|).
Context (g : G) (gnot1 : g ≠ 1).

Let R : G → 'Z_#|G| * 'Z_#|G| → Prop
    := λ A '(x, e), A = g ^ (x + e)^-1%R ∧ x + e ≠ 0.

Program Definition inverse_prot : sigma 'Z_#|G| R NoErr :=
  Iff _ (DepHomPrime (G := 'Z_#|G| * 'Z_#|G|) _ (λ _, g) (λ A '(x, e), A ^ (x + e)) _).
Obligation 1.
  move=> A [x e]. split.
  - move=> [H1 H2].
    apply expgr_eq_div_r in H1 => //.
    by apply Z_is_unit_prime.
  - rewrite /= expgrD -expgrD => H0.
    assert (H1 : x + e ≠ 0).
    { move=> H1. by rewrite H1 expgr0 in H0. }
    split => //.
    symmetry in H0.
    apply expgr_eq_l => //.
    by apply Z_is_unit_prime.
Qed.

End Inverse.
