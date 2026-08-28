From SigmaZK Require Import Base Groups Sigma
  DepHom OR WitnessMap Pedersen Common ECAdd. 

Definition CDM {H W C B : finType}
  {R : H → W → Prop} {E : B → Prop} (P : sigma C R E) :=
  sigma C (λ '(h, a) '(e, z), P.(verify) h a e z) NoErr.

Program Definition ZK {H W : finType} {C} {B : finType}
  {R : H → W → Prop} {E : B → Prop} (P : sigma 'Z_C R E) (P' : CDM P) :
  sigma 'Z_C (λ '(h, a) w, case (R h) (λ '(e, z), P.(verify) h a e z) w) E :=
  (Map (R' := λ ha w, case (R ha.1) (λ ez, P.(verify) ha.1 ha.2 ez.1 ez.2) w)
    id id inl _ _
    (OR (Map fst id inl _ _ P) (Weaken (of_void _) _ (Map id id inl _ _ P')))).
Obligation 1. intros. destruct h, w => //. by destruct p. Qed.
Obligation 2. intros. destruct h, w => //. by destruct p. Qed.
Obligation 6. intros. by destruct h, w. Qed.
Obligation 7. intros. by destruct h, w. Qed.

Program Definition CDM_Pedersen {H W C B R E G G'} f Hf P
  : CDM P → CDM (@Pedersen H W B C G G' R E f Hf P) :=
  Map (λ '(h, (a, A)), ((h, A), a)) id inl _ _.
Obligation 1. intros. by move: h w H0 => [h [a A]] [e z]. Qed.
Obligation 2. intros. by move: h w H0 => [h [a A]] [e z]. Qed.

Definition CDM_WitnessMap {H W W' B C R R' E} toW fromW com sou P
  : CDM P → CDM (@WitnessMap H W W' B C R R' E toW fromW com sou P) := id.

Definition CDM_Iff {H W B C R R' E} iff P
  : CDM P → CDM (@Iff H W B C R R' E iff P) := id.

(* Does this generalize to DepHom? *)
Program Definition CDM_DepHomPrime {B E} {G H : finGroupType} {I q}
  P F primeq HomF ElH (HC : ∀ x y, @commute H x y) :
  CDM (@DepHomPrime B E G H I q P F primeq HomF ElH) :=
  Iff _ (@DepHomPrime _ _ _ _ _ q (λ '(h, a), a^-1)
    (λ '(h, a) '(e, z), P h ^+ nat_of_ord e * (F h z)^-1) _ _ _).
Obligation 1.
  intros. move: h w => [h a] [e z]. split.
  - move=> /eqP ->. by rewrite invMg mulKVg.
  - move=> H1. apply /eqP. apply mulg_eq_inv_l. by rewrite H1 mulgKV.
Qed.
Obligation 3.
  intros. move: i => [h a].
  apply let_pair_dep_Hom => //.
  apply mulg_Hom; try exact _.
  - apply (comp_Hom (λ x, P h ^+ nat_of_ord x) fst); try exact _.
    intros x y. simpl. rewrite expg_mod.
    2: rewrite Zp_cast ?ElH // prime_gt1 //.
    by rewrite expgD.
  - apply invg_Hom; try exact _; apply comp_Hom; exact _.
Qed.

#[export] Instance commute_prod {G H : finGroupType} {x y : G * H}
  : commute x.1 y.1 → commute x.2 y.2 → commute x y.
Proof.
  intros H1 H2. destruct x, y. unfold commute.
  by rewrite 2!mulg_prod H1 H2 /=.
Qed.

Program Definition ECAdd_CDM (G : finGroupType) primeG (g h : G) hgen
  : CDM (ECAdd_Circuit G primeG g h hgen) :=
  CDM_Pedersen _ _ _ (
  CDM_Pedersen _ _ _ (
  CDM_Pedersen _ _ _ (
  CDM_Pedersen _ _ _ (
  CDM_Pedersen _ _ _ (
  CDM_Pedersen _ _ _ (
  CDM_WitnessMap _ _ _ _ _ (
  CDM_Iff _ _ (
  CDM_DepHomPrime _ _ _ _ _ _
  )))))))).

Optimize Heap.

Definition ECAdd_ZK (G : finGroupType) primeG (g h : G) hgen
  := ZK _ (ECAdd_CDM G primeG g h hgen).


Section CountingGroupElements.
  Context (G : finGroupType) (primeG : prime #|G|)
    (g h : G) (hgen : generator [set: G] h).

  Goal (ECAdd_CDM G primeG g h hgen).(Mes).
  Proof. intros. cbn. Abort. (* 15 group elements *)

  Goal (ECAdd_Circuit G primeG g h hgen).(Mes).
  Proof. intros. cbn. Abort. (* 21 group elements*)

  Goal (ECAdd_ZK G primeG g h hgen).(Mes).
  Proof. intros. cbn. Abort. (* 21 + 15 = 36 group elements *)
End CountingGroupElements.
