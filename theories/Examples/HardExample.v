From SigmaZK Require Import Base Groups Sigma DepHom Pedersen WitnessMap Common.

Program Definition R1_Protocol {G : finGroupType}
  (primeG : prime #|G|) (g h : G)
  : sigma 'Z_#|G| (λ '(A, B) '(x, y, z),
      A = g ^ (x ^ 2) * h ^ y ∧ B = g ^ x * h ^ z) NoErr :=
  (WitnessMap (Wit' := 'Z_#|G| ^ 3)
    (λ '(x, y, z), (x, - (z * x) + y, z))
    (λ '(x, y, z), inl (x, z * x + y, z))
    _ _
    (DepHomPrime _ id
      (λ '(A, B) '(x, y, z), (B ^ x * h ^ y, g ^ x * h ^ z)) _)
  ).
Obligation 1.
  move=> G primeG g h
    /= [A B] [[x y] z] [HA HB]; subst.
  apply pair_equal_spec.
  split; [ | reflexivity ].
  by rewrite expgrMn -2!expgrM -mulgA -expgrD GRing.addNKr.
Qed.
Obligation 2.
  move=> G primeG g h
    /= [A B] [[x y] z] [HA HB]; subst.
  split; [ | reflexivity ].
  by rewrite expgrMn -2!expgrM -mulgA -expgrD.
Qed.

Program Definition R2_Protocol {G : finGroupType}
  (primeG : prime #|G|) (g h : G) (gen_h : generator [set: G] h)
  : sigma 'Z_#|G| (λ A '(x, y), A = g ^ (x ^ 2) * h ^ y) NoErr :=
  (Pedersen_expg h (λ '(x, y), g ^ x) _ _
    (WitnessMap id inl _ _ (R1_Protocol primeG g h))
  ).
Obligation 3. by intros ? ? ? ? ? [A B] [[x y] z]. Qed.
Obligation 4. by intros ? ? ? ? ? [A B] [[x y] z]. Qed.
