From SigmaZK Require Import Base Groups Sigma DepHom Common Adjust.

Program Definition GQBase
  (m : nat) (e : nat) (eprime : prime e) :
  sigma 'Z_e (λ z (x : 'Z*_m), z = x ^+ e) NoErr :=
  DepHom e (λ z, z) (λ _ x, x ^+ e) id _ _ _.
Obligation 1. intros. apply gcdz_prime_diff_Z => //. Qed.

Program Definition GuillouQuisquater (lam : nat)
  (m : nat) (e : nat) (eprime : prime e) :
  sigma 'Z_(2 ^ lam)
    (λ z (x : 'Z*_m), z = x ^+ e) NoErr
  := Adjust (GQBase m e eprime) _.

Program Definition FiatShamir (lam m : nat) :
  sigma 'Z_(2 ^ lam) (λ z x, z = x ^+ 2) NoErr
  := GuillouQuisquater lam m 2 _.
