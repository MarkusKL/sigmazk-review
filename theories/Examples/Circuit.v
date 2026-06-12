From SigmaZK Require Import Base Groups Sigma DepHom Pedersen WitnessMap Common.

Section Circuit.

Context (G : finGroupType) (primeG : prime #|G|).
Context (g h : G).

Let Com x r := g ^ x * h ^ r.

Definition Add_Circuit
  : sigma 'Z_#|G| (λ '(C1, C2, C3) '(w1, w2, w3, r1, r2, r3),
      w3 = w1 + w2 ∧ C1 = Com w1 r1 ∧ C2 = Com w2 r2 ∧ C3 = Com w3 r3) NoErr.
Proof.
  eapply (WitnessMap (Wit' := 'Z_#|G| ^ 5)
    (λ '(w1, w2, w3, r1, r2, r3), (w1, w2, r1, r2, r3))
    (λ '(w1, w2, r1, r2, r3), inl (w1, w2, w1 + w2, r1, r2, r3))).
  3: eapply (DepHomPrime _ id
      (λ _ '(w1, w2, r1, r2, r3), (Com w1 r1, Com w2 r2, Com (w1 + w2) r3)) primeG).
  1,2: simpl.
  - by move=> [[C1 C2] C3] [[[[[w1 w2] w3] r1] r2] r3] [] -> [] -> [] -> ->.
  - move=> [[C1 C2] C3] [[[[w1 w2] r1] r2] r3] H.
    do 2 apply pair_equal_spec in H as [H ?]; by subst.
Qed.

Definition Add3_Circuit
  : sigma 'Z_#|G| (λ '(C1, C2, C5)
      '(w1, w2, w3, w4, w5, r1, r2, r5),
      w3 = w1 + w2 ∧ w4 = w1 + w3 ∧ w5 = w4 + w2 ∧
      C1 = Com w1 r1 ∧ C2 = Com w2 r2 ∧ C5 = Com w5 r5) NoErr.
Proof.
  eapply (WitnessMap (Wit' := 'Z_#|G| ^ 5)
    (λ '(w1, w2, _, _, _, r1, r2, r5), (w1, w2, r1, r2, r5))
    (λ '(w1, w2, r1, r2, r5),
      inl (w1, w2, w1 + w2, w1 + (w1 + w2), (w1 + (w1 + w2)) + w2
          , r1, r2, r5))).
  3: eapply (DepHomPrime _ id
      (λ _ '(w1, w2, r1, r2, r5), (Com w1 r1, Com w2 r2, Com ((w1 + (w1 + w2)) + w2) r5)) primeG).
  1,2: simpl.
  - move=> [] [] C1 C2 C5.
    move=> [] [] [] [] [] [] [] w1 w2 w3 w4 w5 r1 r2 r5.
    by move=> [] -> [] -> [] -> [] -> [] -> ->.
  - move=> [] [] C1 C2 C5.
    move=> [] [] [] [] w1 w2 r1 r2 r5 H.
    do 2 apply pair_equal_spec in H as [H ?]; by subst.
Qed.

End Circuit.
