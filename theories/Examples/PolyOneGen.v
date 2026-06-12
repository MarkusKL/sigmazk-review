From SigmaZK Require Import Base Groups Sigma DepHom Pedersen WitnessMap Common.


Fixpoint expG (T : finGroupType) (n : nat) : finGroupType
  := match n with
     | 0 => 'I_1
     | n.+1 => expG T n * T
     end.

Notation " T ^ n " := (expG T n) : type_scope.

#[export] Instance expG_elem_order {G m n} :
  ElemOrder G n → ElemOrder (G ^ m) n.
Proof.
  move=> H x. induction m.
  { destruct (fintype1 (card_ord 1)) as [y E]. by rewrite 2!E. }
  by apply prod_elem_order.
Qed.

Inductive Homs {G H : finGroupType} : seq (G → H) → Type :=
  | Hom_nil : Homs [::]
  | Hom_cons : ∀ f r, Hom f → Homs r → Homs (cons f r).

Existing Class Homs.
Existing Instance Hom_nil.
Existing Instance Hom_cons.

Section PolyOneGen.
Context {G : finGroupType}.
Context (prime_G : prime #|G|).
Context (g h : G).
Context (hgen : generator [set: G] h).

Definition mul_seq {W : finGroupType} : seq (W → 'Z_#|G|) → W → 'Z_#|G| :=
    λ l w, foldr (λ f x, x * f w)%R 1%R l.

Context {Forb : finType} {Err : Forb → Prop}.

Program Fixpoint poly_sigma_lemma (H : finType) k n m
  (P : H → G ^ m) (P1 : H → G) (F : H → 'Z_#|G| ^ n * 'Z_#|G| ^ k → G ^ m) T
  (HHom : ∀ i, Hom (F i)) (HHoms : Homs T) :
  sigma 'Z_#|G| (λ h' w, P h' = F h' (w.1.1, w.2)
    ∧ P1 h' = g ^ (mul_seq T w.2) * h ^ w.1.2) Err :=
  match HHoms with
  | Hom_nil =>
      Iff _
        (@DepHomPrime _ _ _ _ _ _
          (λ h', (P h', g ^ (- 1) * P1 h'))
          (λ h' w, (F h' (w.1.1, w.2), h ^ w.1.2)) _ _ _)
  | Hom_cons a T Ha HT =>
      (Pedersen_expg h (λ w, g ^ mul_seq T w.2) hgen prime_G
        (WitnessMap
          (Wit' := 'Z_#|G| ^ n.+2 * 'Z_#|G| ^ k)
          (λ '(M, r', x, r), (M, - (r * a x) + r', r, x)%R)
          (λ '(M, y, r, x), inl (M, (r * a x) + y, x, r))
          _ _
          (poly_sigma_lemma (H * G)%type k n.+1 m.+1
            (λ h, (P h.1, P1 h.1)) snd
            (λ h' w, (F h'.1 (w.1.1, w.2), h'.2 ^ a w.2 * h ^ w.1.2))
            T _ _
          )))
  end.
Obligation 1.
  intros. move: h0 => h'.
  eapply iff_trans.
  2: apply iff_sym, pair_equal_spec.
  split.
  + intros [H1 H2].
    split => //.
    by rewrite H2 mulgA -expgrD GRing.addNr expgr0 mul1g.
  + intros [H1 H2].
    split => //.
    by rewrite -H2 mulgA -expgrD GRing.addrN expgr0 mul1g.
Qed.
Obligation 3.
  intros. apply prod_Hom;[ by apply comp_Hom | exact _].
Qed.
Obligation 4.
  move=> H k n m P P1 F T' ? ? a T ? ?.
  move=> [A B] [[[M r'] x] r] [[H1 H2] H3] /=.
  rewrite H1 H3. split => //=.
  apply pair_equal_spec. split => //=.
  by rewrite H2 expgrMn -2!expgrM -mulgA -expgrD GRing.addNKr.
Qed.
Obligation 5.
  move=> H k n m P P1 F T' ? ? a T ? ?.
  move=> [A B] [[[M y] r] x] /= [[H1 H2] H3].
  rewrite {}H1 {}H2 {}H3. do 2 (split => //=).
  by rewrite expgrMn -2!expgrM -mulgA -expgrD.
Qed.
Obligation 6.
  intros.
  apply prod_Hom.
  + by apply comp_Hom.
  + apply (mulg_Hom _ _ _).
    1,2: apply expgr_Hom.
    2: exact _.
    apply comp_Hom; try done.
Qed.

Program Definition poly_sigma {H : finType} k
  (P1 : H → G) T {HHoms : Homs T} :
    sigma 'Z_#|G| (λ h' (w : 'Z_#|G| ^ 1 * 'Z_#|G| ^ k),
      P1 h' = g ^ (mul_seq T w.2) * h ^ w.1.2) Err :=
  Iff _ (@poly_sigma_lemma H k 0 0 (fun=> 0) P1 (fun _ _ => 0) T _ _).
Obligation 1.  intros. split; [ done | by move=> [_ ?]].  Qed.

End PolyOneGen.


Section PolyOneGenPure.
Context (G : finGroupType).
Context (prime_G : prime #|G|).
Context (g h : G).
Context (hgen : generator [set: G] h).

Let Err := λ e : 'Z_#|G|, g ^ e = h.

Program Definition poly_sigma_pure {H : finType} k
  (P1 : H → G) T {HHoms : Homs T} :
    sigma 'Z_#|G| (λ h' (w : 'Z_#|G| ^ k), P1 h' = g ^ (mul_seq T w)) Err :=
  Pedersen_expg h (λ w, g ^ mul_seq T w) hgen prime_G (
    WitnessMap
      (Wit' := 'Z_#|G| ^ 3 * 'Z_#|G| ^ k)
      (R' := λ '(A, B) '(_, t, r, r', w),
        (0 : 'I_1, P1 A, B^-1 * P1 A) = (0, g ^ t, h ^ r)
          ∧ B = g ^ mul_seq T w * h ^ r')
      (λ '(w, r), (0, mul_seq T w, - r, r, w))
      (λ '(_, t, r, r', w),
        if (r' + r == 0)%R then
          inl (w, r')
        else
          inr ((t - mul_seq T w) / (r' + r))%R
      ) _ _ (
      Iff _ (
        @poly_sigma_lemma G prime_G g h hgen _ Err (H * G) k 2 2
          (fun AB => (0, P1 AB.1, AB.2^-1 * P1 AB.1))
          snd (fun AB '(_, t, r, w) => (0, g ^ t, h ^ r)) T _ _
  ))).
Obligation 1.
  intros H k P1 T HHoms. 
  intros [A B] [w r] [H1 H2].
  split => //.
  f_equal; [ f_equal |]; try done.
  apply (mulgI B). rewrite mulKVg.
  by rewrite H2 -mulgA -expgrD GRing.subrr expgr0 mulg1.
Qed.
Obligation 2.
  intros H k P1 T HHoms. 
  intros [A B] [[[[_ t] r] r'] w] [H1 H2].
  apply pair_equal_spec in H1 as [H1 H3].
  apply pair_equal_spec in H1 as [_ H1].
  destruct (r' + r == 0) eqn:E; cbn [case].
  + split => //.
    rewrite -(mulKVg B (P1 A)).
    rewrite H3 H2 -mulgA -expgrD in H1 |- *.
    move: E => /eqP ->.
    by rewrite expgr0 mulg1.
  + rewrite -(mulKVg B (P1 A)) in H1.
    rewrite H3 H2 -mulgA -expgrD in H1.
    rewrite /Err expgrM.
    rewrite GRing.addrC.
    rewrite expgrD -H1 mulgA -expgrD GRing.addNr expgr0 mul1g -expgrM.
    rewrite GRing.mulrV // Z_is_unit_prime //.
    apply /eqP. by rewrite E.
Qed.
Obligation 3.
  intros H k P1 T HHoms. 
  move=> /= [A B] [[[[z t] r] r'] w] //.
Qed.


(* Examples *)

Definition rules :=
  (@GRing.mulrA, @GRing.mulr1, @GRing.mul1r, @exprSzr, @expr0z).

Ltac destruct_pair :=
  lazymatch goal with
  | x : _ * _ |- _ => destruct x
  end.

Obligation Tactic :=
  try (simpl; intros; repeat destruct_pair; by rewrite //= !rules).

Let R : G → 'Z_#|G| ^ 1 → Prop
  := λ A '(_, x), A = g ^ (x ^ 2)%R.

Program Definition square_prot : sigma 'Z_#|G| R Err :=
  Iff _ (@poly_sigma_pure G 1 id [:: snd; snd] _).

Let R' : G → 'Z_#|G| ^ 1 → Prop
  := λ A '(_, x), A = g ^ (x ^ 4)%R.

Program Definition quad_prot : sigma 'Z_#|G| R' Err :=
  Iff _ (@poly_sigma_pure G 1 id [:: snd; snd; snd; snd] _).

Let R4 : G → 'Z_#|G| ^ 2 → Prop
  := λ A '(_, x, y), A = g ^ (x * y ^ 2)%R.

Program Definition R4_prot : sigma 'Z_#|G| R4 Err :=
  Iff _ (@poly_sigma_pure G 2 id [:: snd; snd; snd \o fst ] _).

End PolyOneGenPure.
