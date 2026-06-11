From SigmaZK Require Import Base Groups Sigma DepHom WitnessMap Common.

Program Definition ChaumPedersen (G : finGroupType)
  (primeG : prime #|G|) (g1 g2 : G)
  : sigma 'Z_#|G| (λ '(A, B) x, A = g1 ^ x ∧ B = g2 ^ x) NoErr
  := Iff _ (DepHomPrime _ id (λ '(A, B) x, (g1 ^ x, g2 ^ x)) primeG).
Obligation 1.
  intros ? ? ? ? [A B] x. apply iff_sym. apply pair_equal_spec.
Qed.
