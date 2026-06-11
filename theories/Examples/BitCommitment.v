From SigmaZK Require Import
  Base Groups Sigma DepHom Pedersen WitnessMap Common OR.

Section BitCommitment.

Context (G : finGroupType) (primeG : prime #|G|).
Context (g h : G).

Let Com x r := g ^ x * h ^ r.

Program Definition BitCommitment :
  sigma 'Z_#|G| (λ C '((b, r) : bool * _), C = Com b%:R r) NoErr :=
  WitnessMapNoErr
    (R' := λ C w, case (λ r, g ^ (- 1) * C = h ^ r) (λ r, C = h ^ r) w)
    (λ '(b, r), if b then inl r else inr r)
    (λ 'w, case (λ r, (true, r)) (λ r, (false, r)) w) _ _
    (OR
      (DepHomPrime _ (λ C, g ^ (-1) * C) (λ _ r, h ^ r) primeG)
      (DepHomPrime _ (λ C, C) (λ _ r, h ^ r) primeG)
    ).
Obligation 1.
  move=> /= C [[] r] -> /=.
  1: by rewrite /Com mulgA -expgrD GRing.addNr expgr0 mul1g.
  1: by rewrite /Com expgr0 mul1g.
Qed.
Obligation 2.
  unfold Com. move=> /= C [r|r] /= <-.
  1: by rewrite mulgA -expgrD GRing.addrN expgr0 mul1g.
  1: by rewrite expgr0 mul1g.
Qed.

End BitCommitment.
