From SigmaZK Require Import Base Groups Sigma DepHom Common.

Program Definition Okamoto (G : finGroupType)
  (primeG : prime #|G|) (g1 g2 : G)
  : sigma 'Z_#|G| (λ h w, h = g1 ^ w.1 * g2 ^ w.2) NoErr
  := DepHomPrime _ _ _ _.
