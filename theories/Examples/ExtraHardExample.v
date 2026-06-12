From SigmaZK Require Import Base Groups Sigma DepHom Pedersen WitnessMap Common.


Section ExtraHardExample.

Context {G : finGroupType} {g h : G} {prime_G : prime #|G|}.

Let R : G * G → 'Z_#|G| * 'Z_#|G| → Prop := λ '(A, B) '(x, y),
  A = g ^ (x ^ 2)%R * h ^ y ∧ B = g ^ x * h ^ (y ^ 2)%R.

Let R' : G ^ 2 → 'Z_#|G| ^ 6 → Prop
    := λ '(A, B) '(x, y, s, t, u, v),
    A = g ^ t * h ^ y ∧ B = g ^ x * h ^ s ∧
    A = B ^ x * h ^ u ∧ B = A ^ y * g ^ v.

Let Err := λ e : 'Z_#|G|, g ^ e = h.

Lemma expg_sub_eq_l {H : finGroupType} {x : 'Z_#|H|} {h1 h2 h3 : H}
  : h1 ^ x * h2 = h3 → h2 = h1 ^ (- x)%R * h3.
Proof. intros H'. by rewrite -H' mulgA -expgrD GRing.addrC GRing.subrr gsimp. Qed.

Lemma expg_sub_eq_r {H : finGroupType} {x : 'Z_#|H|} {h1 h2 h3 : H}
  : h1 * h2 ^ x = h3 → h1 = h3 * h2 ^ (- x)%R.
Proof. intros H'. by rewrite -H' -mulgA -expgrD GRing.subrr gsimp. Qed.

Program Definition sigmaR : sigma 'Z_#|G| R Err :=
  WitnessMap (Wit' := 'Z_#|G| ^ 6)
    (λ '(x, y), (x, y, y ^ 2, x ^ 2, - (y ^ 2 * x) + y, x - x ^ 2 * y)%R)
    (λ '(x, y, s, t, u, v),
      if (s * x + u == y)%R then
        if (s == y ^ 2)%R then
          inl (x, y)
        else
          inr ((v + t * y - x) / (s - y ^ 2))%R
      else
        inr ((t - x ^ 2) / (s * x + u - y))%R
    ) _ _
    (DepHomPrime _
        (λ '(A, B), (A, B, A, B))
        (λ '(A, B) '(x, y, s, t, u, v),
          (g ^ t * h ^ y, g ^ x * h ^ s, B ^ x * h ^ u, g ^ v * A ^ y)) _).
Obligation 1.
  move=> /= [A B] [x y] [H1 H2].
  repeat f_equal => //; subst.
  - rewrite expgrMn expgrM -mulgA. f_equal.
    by rewrite -expgrM -expgrD GRing.addNKr.
  - rewrite expgrMn -2!expgrM mulgA. f_equal.
    by rewrite -expgrD GRing.addrNK.
Qed.
Obligation 2.
  move=> /= [A B] [[[[[x y] s] t] u] v] H.
  apply pair_equal_spec in H as [H H4].
  apply pair_equal_spec in H as [H H3].
  apply pair_equal_spec in H as [H1 H2]. subst.
  rewrite expgrMn -2!expgrM -mulgA -expgrD in H3.
  rewrite expgrMn -2!expgrM mulgA -expgrD in H4.
  destruct (s * x + u == y)%R eqn:E.
  2: {
    cbn [case]. rewrite /Err expgrM.
    apply esym, expg_sub_eq_l, esym in H3.
    rewrite mulgA -expgrD GRing.addrC in H3.
    apply expg_sub_eq_r in H3.
    rewrite -expgrD in H3.
    rewrite H3 -expgrM GRing.mulrV //.
    apply Z_is_unit_prime => // H.
    move: E => /eqP E. apply E.
    by rewrite -(GRing.subrK y (s * x + u)) H GRing.add0r.
  }
  destruct (s == y ^ 2)%R eqn:E'; rewrite E'.
  2: {
    cbn [case]. rewrite /Err expgrM.
    apply expg_sub_eq_l in H4.
    rewrite mulgA -expgrD GRing.addrC in H4.
    apply esym, expg_sub_eq_r, esym in H4.
    rewrite -expgrD in H4.
    rewrite -H4 -expgrM GRing.mulrV //.
    apply Z_is_unit_prime => // H.
    move: E' => /eqP E'. apply E'.
    by rewrite -(GRing.subrK (y * y)%R s) H GRing.add0r.
  }
  move: E E' => /eqP E /eqP E'.
  split.
  - by rewrite {}H3 E.
  - by rewrite E'.
Qed.

End ExtraHardExample.
