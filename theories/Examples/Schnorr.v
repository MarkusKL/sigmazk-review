From SigmaZK Require Import Base Groups Sigma DepHom Common.

Program Definition Schnorr 
  (G : finGroupType) (primeG : prime #|G|) (g : G)
  : sigma 'Z_#|G| (λ h (w : 'Z_#|G|), h = g ^ w) NoErr
  := DepHomPrime _ _ _ _.
