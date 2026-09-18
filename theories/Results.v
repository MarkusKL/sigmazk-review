From SigmaZK Require Import Base Groups Sigma
  OR AND DepHom WitnessMap Pedersen Shrink Parallel
  Schnorr Okamoto ChaumPedersen HardExample
  Square ExtraHardExample Inverse PolyOneGen
  BBSPlusPoK Circuit Adjust GuillouQuisquater
  BitCommitment EQ ECAdd CDM.

(* This file prints our results to the the output,
   so that they are visible while compiling and checking. *)

Definition Firstly_the_type_of_sigma := tt.
Check Firstly_the_type_of_sigma.

Check @sigma.

Definition Secondly_our_7_composition_rules := tt.
Check Secondly_our_7_composition_rules.

Check @OR.
Check @AND.
Check @DepHom.
Check @WitnessMap.
Check @Pedersen.
Check @Shrink.
Check @Parallel.

Definition Thirdly_our_17_examples := tt.
Check Thirdly_our_17_examples.

Section ForNotation.
Local Notation fZ G := (fintype_ordinal__canonical__fintype_Finite (Zp_trunc #|G|).+2).
Local Notation "G × H" := (Datatypes_prod__canonical__fintype_Finite G H) (at level 21, left associativity).

Check @Schnorr.
Check @Okamoto.
Check @ChaumPedersen.
Check @R1_Protocol.
Check @R2_Protocol.
Check @square_prot.
Check @sigmaR.
Check @inverse_prot.
Check @poly_sigma_pure.
Check @BBSPlusPoK.
Check @BBS2.
Check @Adjust.
Check @GuillouQuisquater.
Check @BitCommitment.
Check @EQ.
Check @ECAdd_Circuit.
Check @ECAdd_ZK.

End ForNotation.

Definition Fourthly_our_rules_and_examples_use_no_axioms := tt.
Check Fourthly_our_rules_and_examples_use_no_axioms.

Definition rules_and_examples := (
  @OR , @AND , @DepHom, @WitnessMap, @Pedersen, @Shrink, @Parallel,
  @Schnorr, @Okamoto, @ChaumPedersen, @R1_Protocol, @R2_Protocol,
  @square_prot, @sigmaR, @inverse_prot, @poly_sigma_pure,
  @BBSPlusPoK, @BBS2, @Adjust, @GuillouQuisquater, @BitCommitment, @EQ,
  @ECAdd_Circuit, @ECAdd_ZK ).

Print Assumptions rules_and_examples.


Definition Fifthly_our_results_in_NSSProve := tt.
Check Fifthly_our_results_in_NSSProve.

From SigmaZK Require Import Scheme Properties.
From SSProve.Crypt Require Import NominalPrelude.
Import PackageNotation.
#[local] Open Scope package_scope.

Check @sigma_Complete.
Check @sigma_SHVZK.
Check @sigma_Special_Soundness.

Definition nssp_results :=
  ( @sigma_Complete, @sigma_SHVZK, @sigma_Special_Soundness ).

Print Assumptions nssp_results.
Definition Axioms_above_are_the_same_as_those_of_SSProve := tt.
Check Axioms_above_are_the_same_as_those_of_SSProve.
