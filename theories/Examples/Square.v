From SigmaZK Require Import Base Groups Sigma DepHom Pedersen WitnessMap Common.


Section Square.
Context (G : finGroupType) (prime_G : prime #|G|).
Context (g h : G) (hgen : generator [set: G] h).

Let R3 : G → 'Z_#|G| → Prop
  := λ A x, A = g ^ (x ^ 2)%R.

Let R3' : G * G → 'Z_#|G| ^ 4 → Prop
  := λ '(A, B) '(x, y, z, t),
      A = g ^ t ∧ B = g ^ x * h ^ z ∧ A = B ^ x * h ^ y.

Let Err := λ e : 'Z_#|G|, g ^ e = h.

Program Definition square_prot : sigma 'Z_#|G| R3 Err :=
  Pedersen_expg h (λ x, g ^ x) _ _
    (WitnessMap (Wit' := 'Z_#|G| ^ 4)
      (λ '(x, r), (x, - (r * x), r, x * x)%R)
      (λ '(x, y, z, t),
        if (z * x + y == 0)%R then
          inl (x, z)
        else
          inr ((t - x * x) / (z * x + y))%R
      ) _ _
      (DepHomPrime (G := 'Z_#|G| ^ 4) _
          (λ '(A, B), (A, B, A))
          (λ '(A, B) '(x, y, z, t),
            (g ^ t, g ^ x * h ^ z, B ^ x * h ^ y)) _)
    ).
Obligation 3.
  move=> /= [A B] [x r] [H1 H2]. subst.
  repeat f_equal => //.
  by rewrite expgrMn -mulgA -2!expgrM -expgrD GRing.subrr expgr0 mulg1.
Qed.
Obligation 4.
  move=> /= [A B] [[[x y] z] t] H.
  apply pair_equal_spec in H as [H E3].
  apply pair_equal_spec in H as [E1 E2].
  subst. rewrite expgrMn -2!expgrM -mulgA -expgrD in E3.
  destruct (z * x + y == 0)%R eqn:E.
  - move: E => /eqP E. rewrite E expgr0 mulg1 in E3.
    by rewrite E3.
  - cbn [case]. rewrite /Err expgrM. rewrite mulgC in E3.
    rewrite expgrD E3 -mulgA -expgrD GRing.subrr expgr0 mulg1 -expgrM.
    rewrite GRing.mulrV // Z_is_unit_prime //.
    apply /eqP. by rewrite E.
Qed.

End Square.
