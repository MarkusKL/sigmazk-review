From SigmaZK Require Import Base.
From mathcomp Require Export all_fingroup solvable.cyclic.
#[global] Open Scope ring_scope. Export GroupScope.


#[global] Bind Scope type_scope with finGroupType.

Section GroupLemmas.

Context [G : finGroupType].

(* Exponent modulo order of G *) 
Lemma expg_card (x : G) : x ^+ #|G| = 1.
Proof. rewrite -cardsT expg_cardG //=. Qed.

Lemma expg_trunc (x : G) : x ^+ (Zp_trunc #|G|).+2 = 1.
Proof.
  destruct #|G| eqn:E => //=.
  { by apply fintype0 in E. }
  destruct n eqn:En => //=; subst.
  { apply fintype1 in E as [g' E].
    by rewrite 2!E. }
  rewrite Zp_cast // -E expg_card //.
Qed.

Lemma expg_mod_trunc (x : G) (a : nat)
  : x ^+ (a %% (Zp_trunc #|G|).+2) = x ^+ a.
Proof. rewrite expg_mod // expg_trunc //. Qed.


(* Exponent in ring module order of G *)

Definition expgr : G → 'Z_#|G| → G
  := λ x r, expgn x r.

Arguments expgr _%_g _%_R.

Notation "x ^ z" :=
  (expgr x%g z%R) : group_scope.

Lemma expgr0 (x : G) : x ^ 0 = 1.
Proof. done. Qed.

Lemma expgr1 (x : G) : x ^ 1 = x.
Proof. done. Qed.

Lemma expgrn (x : G) (n : nat) : x ^+ n = x ^ n%:R.
Proof. by rewrite /expgr Zp_nat /= expg_mod_trunc. Qed.

Lemma expgrD (x : G) (a b : 'Z_#|G|) : x ^ (a + b) = x ^ a * x ^ b.
Proof. rewrite /expgr expg_mod_trunc expgD //. Qed.

Lemma expgrM (x : G) (a b : 'Z_#|G|) : x ^ (a * b) = (x ^ a) ^ b.
Proof. rewrite /expgr expg_mod_trunc expgM //. Qed.

Lemma expgrMn (x y : G) (a : 'Z_#|G|) (Hcom : commute x y)
  : (x * y) ^ a = x ^ a * y ^ a.
Proof. rewrite /expgr expgMn //. Qed.

Lemma expgrN1 (x : G) : x ^ (- 1) = x^-1.
Proof.
  apply (mulgI (x ^ 1)).
  by rewrite -expgrD GRing.subrr expgr0 expgr1 mulgV.
Qed.

Lemma expgrN (x : G) (a : 'Z_#|G|) : x ^ (- a) = x^-1 ^ a.
Proof. by rewrite -expgrN1 -expgrM GRing.mulN1r. Qed.

Lemma expgrnV (x : G) (n : nat) : x ^- n = x ^ (- n%:R).
Proof. rewrite /expgr -expgVn expgrn -expgrN //. Qed.


(* Exponent in int *)

Definition expgz : G → int → G := λ g z,
  match z with
  | Posz n => g ^+ n
  | Negz n => g ^- n.+1
  end.

Notation "x ^ z" :=
  (expgz x z) : group_scope.

Lemma expgz_pos {x : G} {n} : x ^+ n = x ^ (n%:Z).
Proof. done. Qed.

Lemma expgz_neg {x : G} {n} : x ^- n = x ^ (- n%:Z).
Proof. destruct n => //=. rewrite expg0 invg1 //. Qed.

Lemma expgzD1 {x : G} {z : int}
  : x ^ (1 + z) = x * x ^ z.
Proof.
  destruct z => /=.
  - rewrite add1n expgS //.
  - rewrite {1}NegzE intS.
    rewrite -expgVn expgS expgVn.
    rewrite GRing.opprD GRing.addrA.
    rewrite GRing.subrr GRing.add0r.
    rewrite mulKVg expgz_neg //.
Qed.

Lemma expgz_neg1 {x : G} {z : int} : x^-1 ^ (- z) = x ^ z.
Proof.
  destruct z.
  - rewrite -expgz_neg -expgVn invgK //.
  - rewrite NegzE GRing.opprK -expgz_pos.
    rewrite -expgz_neg -expgVn //.
Qed.

Lemma expgzDn {x : G} {n : nat} {z' : int}
  : x ^ (n%:Z + z') = x ^+ n * x ^ z'.
Proof.
  induction n => /=.
  - rewrite GRing.add0r expg0 mul1g //.
  - rewrite intS -GRing.addrA.
    rewrite expgzD1 IHn mulgA expgS //.
Qed.

Lemma expgzD {x : G} {z z' : int}
  : x ^ (z + z') = x ^ z * x ^ z'.
Proof.
  destruct z; [ by rewrite expgzDn |].
  rewrite NegzE -expgz_neg1.
  rewrite GRing.opprD GRing.opprK expgzDn.
  rewrite -expgz_neg expgVn expgz_neg1 //.
Qed.

Lemma expgzMn {x : G} {z : int} {n : nat}
  : x ^ (z * n%:Z) = (x ^ z) ^+ n.
Proof.
  induction n.
  - by rewrite GRing.mulr0 /= 2!expg0.
  - rewrite intS.
    rewrite GRing.mulrDr GRing.mulr1.
    rewrite expgzD IHn -expgS //.
Qed.

Lemma expgzM {x : G} {z z' : int}
  : x ^ (z * z') = (x ^ z) ^ z'.
Proof.
  destruct z'; [ by rewrite expgzMn |].
  rewrite NegzE GRing.mulrN.
  rewrite -expgz_neg1 GRing.opprK expgzMn.
  rewrite -expgz_neg -expgVn /=.
  f_equal. destruct z; by rewrite /= expgVn.
Qed.

End GroupLemmas.

Notation "x ^ z" :=
  (expgr x%g z%R) : group_scope.


Section GroupEqLemmas.
Context [G : finGroupType].

Lemma mulg_eq_inv_l : ∀ x y z : G, x^-1 * y = z → y = x * z.
Proof. intros x y z <-. by rewrite mulKVg. Qed.

Lemma mulg_eq_r : ∀ x y z : G, y = x * z → x^-1 * y = z.
Proof. intros x y z ->. by rewrite mulKg. Qed.

Lemma mulg_eq_inv_r : ∀ x y z : G, x = y * z^-1 → x * z = y.
Proof. intros x y z ->. by rewrite mulgKV. Qed.

Lemma mulg_eq_l : ∀ x y z : G, x * z = y → x = y * z^-1.
Proof. intros x y z <-. by rewrite mulgK. Qed.

Lemma expgr_eq_l (g h  : G) (x : 'Z_#|G|)
  : x \is a GRing.unit → g ^ x = h → g = h ^ x^-1%R.
Proof. intros HU H'. rewrite -H' -expgrM GRing.mulrV //. Qed.

Lemma expgr_eq_div_r (g h : G) (x : 'Z_#|G|)
  : x \is a GRing.unit → g = h ^ x^-1%R → g ^ x = h.
Proof. intros HU H'. rewrite H' -expgrM GRing.mulVr //. Qed.

End GroupEqLemmas.


Section DiscreteLog.

Context [G : finGroupType].

Definition log (b x : G) (H : x \in <[b]>) : nat :=
  sval (cyclePmin H).

Lemma genT {x y} : generator [set : G] x → y \in <[x]>.
Proof. by move=> /eqP <-. Qed.

Lemma expg_log {x} {y} H : x ^+ (log x y H) = y.
Proof.
  unfold log.
  destruct cyclePmin as [n' H1 H2].
  subst; simpl.
  f_equal.
Qed.

Lemma inv_expg {x} : (1 < #|G|)%N → generator [set : G] x
  → inverse (λ n : 'Z_#|G|, x ^+ n).
Proof.
  intros LT H.
  exists (λ y, inord (log x y (genT H))); split.
  - intros n.
    unfold log.
    destruct cyclePmin as [n' H1 H2].
    simpl.
    move: H2 => /eqP.
    rewrite eq_expg_mod_order => /eqP.
    rewrite (modn_small H1) => <-.
    rewrite modn_small.
    1: apply inord_val.
    rewrite -modZp.
    rewrite {2}Zp_cast //.
    rewrite orderE.
    move: H => /eqP <-.
    rewrite cardsT.
    rewrite ltn_mod.
    by apply ltnW.
  - intros y.
    unfold log.
    destruct cyclePmin as [n' H1 H2].
    subst; simpl.
    f_equal.
    apply inordK.
    rewrite Zp_cast //.
    rewrite -cardsT.
    move: H => /eqP ->.
    by rewrite -orderE.
Qed.

Lemma commute_gen {z x y : G} : generator [set: G] z → commute x y.
Proof.
  intros H.
  rewrite -(@expg_log _ x (genT H)).
  rewrite -(@expg_log _ y (genT H)).
  by apply commuteX2.
Qed.

Lemma cyclic_commute {x y : G} : cyclic [set: G] → commute x y.
Proof. move=> /cyclicP [z H].  apply (@commute_gen z).  by apply /eqP. Qed.

Lemma prime_commute {x y : G} : prime #|G| → commute x y.
Proof. intros. apply cyclic_commute, prime_cyclic. by rewrite cardsT. Qed.

Lemma inv_mulg {x : G} : inverse (mulg x).
Proof.
  exists (mulg x^-1); split.
  - intros y. by rewrite mulKg.
  - intros y. by rewrite mulKVg.
Qed.

Lemma inv_mulg_r {x : G} : inverse (mulg^~ x).
Proof.
  exists (mulg^~ x^-1); split.
  - intros y. by rewrite mulgK.
  - intros y. by rewrite mulgKV.
Qed.

End DiscreteLog.


Section Units.

Lemma Z_is_unit {H : finGroupType} {z : 'Z_#|H|} : (1 < #|H|)%N → coprime #|H| z → z \is a GRing.unit.
Proof. intros. rewrite -(natr_Zp z). rewrite unitZpE //. Qed.

Lemma Z_coprime {H : finGroupType} {z : 'Z_#|H|} : prime #|H| → z ≠ 0 → coprime #|H| z.
Proof.
  intros.
  rewrite prime_coprime //.
  rewrite gtnNdvd //.
  - rewrite lt0n.
    apply /eqP => E4.
    change (0%N) with (nat_of_ord (0%R : 'Z_#|H|)) in E4.
    by apply ord_inj in E4.
  - rewrite -{2}(@Zp_cast #|H|) //.
    by apply prime_gt1.
Qed.

Lemma Z_is_unit_prime {H : finGroupType} {z : 'Z_#|H|} : prime #|H| → z ≠ 0 → z \is a GRing.unit.
Proof.
  intros.
  apply Z_is_unit.
  - by apply prime_gt1.
  - by apply Z_coprime.
Qed.

End Units.


Section HomLemmas.
  Context {G H : finGroupType} (F : G → H).

  Class Hom :=
    Hom_mulg : ∀ x y, F (x * y) = F x * F y.

  Context `{Hom}.

  Lemma Hom1 : F 1 = 1.
  Proof.
    apply (mulgI (F 1)).
    rewrite -Hom_mulg 2!mulg1 //.
  Qed.

  Lemma Hom_invg x : F x^-1 = (F x)^-1.
  Proof.
    apply (mulgI (F x)).
    rewrite -Hom_mulg mulgV mulgV Hom1 //.
  Qed.

  Lemma Hom_expgn x n : F (x ^+ n) = F x ^+ n.
  Proof.
    induction n.
    - rewrite 2!expg0 Hom1 //.
    - rewrite 2!expgS Hom_mulg IHn //.
  Qed.
End HomLemmas.


Section HomInstances.
  Context {G G' H H' : finGroupType}.

  #[export] Instance expgr_Hom (g : G) (F : H → 'Z_#|G|)
    : Hom F → Hom (λ x, g ^ F x).
  Proof. move=> /= HF x y. by rewrite Hom_mulg expgrD. Qed.

  #[export] Instance expgn_Hom_base (e : nat) (F : G → G)
    : (∀ x y, commute (F x) (F y))
    → Hom F → Hom (λ x, F x ^+ e).
  Proof. move=> /= HC HF x y. by rewrite Hom_mulg expgMn. Qed.
  
  #[export] Instance mulg_Hom (F1 F2 : G → H)
    : (∀ x y, commute (F1 x) (F2 y))
    → Hom F1 → Hom F2 → Hom (λ x, F1 x * F2 x).
  Proof.
    move=> /= HC HF1 HF2 x y.
    rewrite 2!Hom_mulg 2!mulgA.
    f_equal. by rewrite -mulgA HC mulgA.
  Qed.

  #[export] Instance invg_Hom (F1 : G → H)
    : (∀ x y, commute (F1 x) (F1 y))
    → Hom F1 → Hom (λ x, (F1 x)^-1).
  Proof.
    intros HC HF1 x y.
    by rewrite -invMg Hom_mulg HC.
  Qed.

  #[export] Instance prod_Hom (F1 : G → H) (F2 : G → H')
    : Hom F1 → Hom F2 → Hom (λ x, (F1 x, F2 x)).
  Proof. intros HF1 HF2 x y. by rewrite HF1 HF2. Qed.

  #[export] Instance id_Hom : @Hom G _ id.
  Proof. done. Qed. 

  (* Cannot add to search as it will match id as left function argument. *)
  Lemma comp_Hom {G1 G2 G3 : finGroupType} F1 F2
    : @Hom G2 G1 F1 → @Hom G3 G2 F2 → Hom (F1 \o F2).
  Proof. move=> HF1 HF2 x y /=. by rewrite HF2 HF1. Qed.

  #[export] Instance fst_Hom (F : G → H * H') : Hom F → @Hom G H (fst \o F).
  Proof. by apply comp_Hom. Qed. 

  #[export] Instance snd_Hom (F : G → H * H') : Hom F → @Hom G H' (snd \o F).
  Proof. by apply comp_Hom. Qed. 

  #[export] Instance ord1_Hom F : @Hom G 'I_1 F.
  Proof. intros x y. by rewrite 2!ord1. Qed.


  #[export] Instance let_pair_Hom {A B : Type} (c : A * B)
    (F : A → B → G → H)
    : Hom (F c.1 c.2) → Hom (let '(x, y) := c in F x y).
  Proof. by destruct c. Qed.

  #[export] Instance let_pair_dep_Hom (p : G → G' * H')
    (F : G' → H' → G → H) : Hom p
    → Hom (λ z, F (p z).1 (p z).2 z) → Hom (λ z, let '(x, y) := p z in F x y z).
  Proof.
    intros Hp HF x y. rewrite Hom_mulg.
    specialize (HF x y).
    rewrite /= in HF.
    rewrite Hom_mulg in HF.
    by destruct (p x), (p y).
  Qed.
End HomInstances.


(* commute as a typeclass *)
Existing Class commute.

#[export] Instance commuteZ (m : nat) : ∀ x y : 'Z_m, commute x y.
Proof.
  intros x y. unfold commute.
  change mulg with (@GRing.add 'Z_m). by rewrite GRing.addrC.
Qed.

Notation " 'Z*_ m " := {unit 'Z_m}
  (at level 8, m at level 2, format "''Z*_' m") : type_scope.

#[export] Instance commuteZm (m : nat) : ∀ x y : 'Z*_m, commute x y.
Proof. intros x y. apply /eqP. rewrite -val_eqE /= GRing.mulrC //. Qed.

#[export] Hint Extern 3 (commute _ _) =>
  eapply prime_commute; eassumption : typeclass_instances.

(* Try to prove commutativity by pointing to a generator. *)
(* Obsolete due to prime_commute
#[export] Hint Extern 3 (commute _ _) =>
  eapply commute_gen; eassumption : typeclass_instances.  *)

Lemma mulgC {G : finGroupType} {x y : G} : commute x y → x * y = y * x.
Proof. done. Qed.


Section GCDLemmas.
Lemma gcdz_prime {p : nat} {d : int}
  : prime p → (0 < `|d|%Z < p)%N → gcdz p d = 1%Z.
Proof.
  move=> Hp /andP Hd.
    rewrite -(GRing.mulr1 d).
  rewrite Gauss_gcdzr ?gcdz1 //.
  rewrite coprimezE /=.
  rewrite prime_coprime //.
  rewrite gtnNdvd //; apply Hd.
Qed.

Lemma absz_sub {e e' l : nat} : (e < l)%N → (e' < l)%N → (`|e - e'| < l)%N.
Proof.
  cut (∀ e e', (e < l)%N → (e' < l)%N → (0 <= e%:Z - e'%:Z) → (`|e - e'| < l)%N).
  - intros H H1 H2.
    destruct (0 <= e%:Z - e'%:Z)%Z eqn:E.
    + rewrite H //.
    + rewrite distnC H //.
      rewrite -GRing.opprB.
      rewrite Num.Theory.lerNr.
      rewrite GRing.oppr0.
      rewrite Num.Theory.real_leNgt //=.
      apply /negP => H'.
      move: E => /negP E.
      apply E.
      by apply Order.POrderTheory.ltW.
  - move=> {}e {}e' He He' H.
    rewrite -ltz_nat gez0_abs //.
    rewrite Num.Theory.ltrBlDl.
    rewrite Num.Theory.ltr_wpDl //.
Qed.

Lemma gcdz_prime_diff {p n n' : nat}
  : prime p → n != n' → (n < p)%N → (n' < p)%N → gcdz p (n%:Z - n'%:Z) = 1%Z.
Proof.
  intros Hp H Hn Hn'.
  rewrite gcdz_prime //.
  apply /andP; split.
  - move: H => /eqP H.
    rewrite lt0n.
    rewrite absz_eq0.
    apply /negP => /eqP H'.
    apply GRing.Theory.subr0_eq in H'.
    move: H' => /eqP.
    by rewrite eqz_nat => /eqP H'.
  - rewrite absz_sub //.
Qed.

Lemma gcdz_prime_diff_Z {p : nat} {e e' : 'Z_p}
  : prime p → e != e' → gcdz p (e%:Z - e'%:Z) = 1%Z.
Proof.
  intros Hp H.
  apply gcdz_prime_diff => // {H};
    apply widen_ord_proof;
    rewrite Zp_cast //;
    by apply prime_gt1.
Qed.
End GCDLemmas.
