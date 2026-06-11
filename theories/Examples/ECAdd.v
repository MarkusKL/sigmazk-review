From SigmaZK Require Import Base Groups Sigma DepHom Pedersen WitnessMap Common.

Section ECAdd.

Open Scope ring_scope.

Context (G : finGroupType) (primeG : prime #|G|).
Context (g h : G) (gen_h : generator [set: G] h).

Notation ZG := ('Z_#|G|).
Definition Com x r := (g ^ x * h ^ r)%g.
Arguments Com _%_R _%_R.

Lemma Cexpgr x r y : (Com x r ^ y = Com (x * y) (r * y))%g.
Proof. by rewrite /Com expgrMn -2!expgrM. Qed.

Lemma Ch x r r' : (Com x r * h ^ r' = Com x (r + r'))%g.
Proof. by rewrite /Com -mulgA -expgrD. Qed.

Lemma Cmulg x y r r' : (Com x r * Com y r' = Com (x + y) (r + r'))%g.
Proof.
  rewrite /Com expgrD -2!mulgA. f_equal.
  rewrite expgrD 2!mulgA. f_equal.
  by rewrite mulgC.
Qed.

Lemma Cinv x r : ((Com x r)^-1 = Com (- x) (- r))%g.
Proof. by rewrite /Com -expgrN1 Cexpgr 2!GRing.mulrN1. Qed.

Definition Csimpl := (@Cmulg, @Cexpgr, @Ch, @Cinv).

Lemma Ceq {x y r r'} :
  Com x r = Com y r' → x - y ≠ 0 → Com 1 ((r - r') / (x - y)) = 1%g.
Proof.
  move=> H H'. apply mulg_eq_l in H.
  rewrite /Com -mulgA in H.  apply mulg_eq_r in H.
  rewrite -2!expgrN1 -2!expgrM 2!GRing.mulrN1 in H.
  rewrite -2!expgrD GRing.addrC in H.
  apply expgr_eq_l in H; [| apply Z_is_unit_prime => // ].
  rewrite /Com expgr1 H -expgrM -expgrD.
  by rewrite -GRing.opprB GRing.mulNr GRing.addNr expgr0.
Qed.

Definition ec_add : ZG * ZG → ZG * ZG → ZG * ZG :=
  λ a b, 
    let tx := (( (b.2 - a.2) / (b.1 - a.1) ) ^ 2 - a.1 - b.1) in
    (tx , ( (b.2 - a.2) / (b.1 - a.1) ) * (b.1 - tx) - a.2).
  (*if a.1 == b.1 then
      (2 * a.1, 2 * a.2)%R
     else*)

Let Err := λ e : 'Z_#|G|, Com 1 e = 1%g. (* h ^ e = g *)

Definition Add_Com {H W B C R E} f :
  sigma C (λ '(h, B) '(w, r), R h w ∧ B = Com (f w) r) E
  → @sigma H W B C R E := Pedersen_expg h (λ w, g ^ f w)%g gen_h primeG.

(* 28 sec ~> 12 sec *)
Program Definition ECAdd_Circuit
  : sigma 'Z_#|G| (λ '(C1, C2, C3, C4, C5, C6)
      '(a, b, t, r1, r2, r3, r4, r5, r6),
      a.1 ≠ b.1 ∧ ec_add a b = t
      ∧ C1 = Com a.1 r1 ∧ C2 = Com a.2 r2 ∧ C3 = Com b.1 r3
      ∧ C4 = Com b.2 r4 ∧ C5 = Com t.1 r5 ∧ C6 = Com t.2 r6) Err :=
(*(Add_Com (λ '(a, b, t, r1, r2, r3, r4, r5, r6),
    (* C7 unused *) b.1 - a.1 ) *)
  (Add_Com (λ '(a, b, t, r1, r2, r3, r4, r5, r6),
    (* C8 *) (b.1 - a.1)^-1 )
(*(Add_Com (λ '(a, b, t, r1, r2, r3, r4, r5, r6, r7, r8),
    (* C9 unused *) b.2 - a.2 )*)
  (Add_Com (λ '(a, b, t, r1, r2, r3, r4, r5, r6
    , r8),
    (* C10 *) (b.2 - a.2) / (b.1 - a.1) )
  (Add_Com (λ '(a, b, t, r1, r2, r3, r4, r5, r6
    , r8, r10),
    (* C11 *) ((b.2 - a.2) / (b.1 - a.1))^2 )
(*(Add_Com (λ '(a, b, t, r1, r2, r3, r4, r5, r6
    , r7, r8, r9, r10, r11),
    (* C12 unused *) b.1 - t.1 ) *)
  (Add_Com (λ '(a, b, t, r1, r2, r3, r4, r5, r6
    , r8, r10, r11),
    (* C13 *) ((b.2 - a.2) / (b.1 - a.1)) * (b.1 - t.1) )
  (Add_Com (λ '(a, b, t, r1, r2, r3, r4, r5, r6
    , r8, r10, r11, r13),
    (* C14 extra *) 1 )
  (Add_Com (λ '(a, b, t, r1, r2, r3, r4, r5, r6
    , r8, r10, r11, r13, r14),
    (* C15 extra *) (b.2 - a.2) ^ 2 / (b.1 - a.1) )
  (WitnessMap
    (R' := λ
      '(C1, C2, C3, C4, C5, C6, C8, C10, C11,  C13, C14, C15)
      '(a, b, t, x, r1, r2, r3, r4, r5, r6
      , r8', r10, r10', r11', r13', r14, r15', r16, r17),
          C1 = Com a.1 r1 ∧ C2 = Com a.2 r2 ∧ C3 = Com b.1 r3
        ∧ C4 = Com b.2 r4 ∧ C5 = Com t.1 r5 ∧ C6 = Com t.2 r6
        ∧ C8 ^ (b.1 - a.1) = C14 * h ^ r8'
        ∧ C10 = C8 ^ (b.2 - a.2) * h ^ r10'
        ∧ C11 ^ (b.1 - a.1) = C15 * h ^ r11'
        ∧ C13 = C10 ^ (b.1 - t.1) * h ^ r13'
        ∧ C14 = Com 1 r14
        ∧ C15 = C10 ^ (b.2- a.2) * h ^ r15'
        ∧ C5 = C11 * C1^-1 * C3^-1 * h ^ r16
        ∧ C6 = C13 * C2^-1 * h ^ r17
        ∧ C10 = Com x r10
    )%g
    (λ '(a, b, t
        , r1, r2, r3, r4, r5, r6, r8, r10, r11, r13, r14, r15),
        (a, b, t, (b.2 - a.2) / (b.1 - a.1)
        , r1, r2, r3, r4, r5, r6
        , r8 * (b.1 - a.1) - r14, r10, r10 - r8 * (b.2 - a.2)
        , r11 * (b.1 - a.1) - r15, r13 - r10 * (b.1 - t.1)
        , r14, r15 - r10 * (b.2 - a.2), - (r11 - r1 - r3) + r5, - (r13 - r2) + r6))
    (λ '(a, b, t, _, r1, r2, r3, r4, r5, r6
        , r8', r10, r10', r11', r13', r14, r15', r16, r17),
        let r8 := (r14 + r8') / (b.1 - a.1) in
        let r10 := r8 * (b.2 - a.2) + r10' in
        let r15 := r10 * (b.2 - a.2) + r15' in
        let r13 := r10 * (b.1 - t.1) + r13' in
        let r11 := (r15 + r11') / (b.1 - a.1) in
        if b.1 - a.1 == 0 then
          inr (r14 + r8')
        else if t.1 - (((b.2 - a.2) / (b.1 - a.1)) ^ 2 - a.1 - b.1) != 0 then
          inr (
            (r5 - (r11 - r1 - r3 + r16))
            /
            (t.1 - (1 / (b.1 - a.1) * (b.2 - a.2)
                   * (b.2 - a.2) / (b.1 - a.1) - a.1 - b.1)))
        else if t.2 - (((b.2 - a.2) / (b.1 - a.1)) * (b.1 - t.1) - a.2) != 0 then
          inr (
            (r6 - (r13 - r2 + r17))
            /
            (t.2 - (1 / (b.1 - a.1) * (b.2 - a.2) * (b.1 - t.1) - a.2)))
        else
          inl (a, b, t, r1, r2, r3, r4, r5, r6
              , r8, r10, r11, r13, r14, r15))
    _ _
  (Iff _
  (DepHomPrime #|G|
    (λ '(C1, C2, C3, C4, C5, C6, C8, C10, C11, C13, C14, C15),
    (C1, C2, C3, C4, C5, C6, C14^-1, C10, C15^-1, C13
    , (C14 * g^-1) , C15, C3 * C1 * C11^-1 * C5, C2 * C13^-1 * C6, C10))%g
    (λ '(C1, C2, C3, C4, C5, C6, C8, C10, C11, C13, C14, C15)
      '(a, b, t, x, r1, r2, r3, r4, r5, r6
      , r8', r10, r10', r11', r13', r14, r15', r16, r17),
      ( Com a.1 r1, Com a.2 r2, Com b.1 r3, Com b.2 r4, Com t.1 r5, Com t.2 r6
      , (C8 ^ (b.1 - a.1))^-1 * h ^ r8'
      , C8 ^ (b.2 - a.2) * h ^ r10'
      , (C11 ^ (b.1 - a.1))^-1 * h ^ r11'
      , C10 ^ (b.1 - t.1) * h ^ r13', h ^ r14, C10 ^ (b.2 - a.2) * h ^ r15'
      , h ^ r16, h ^ r17, Com x r10
      )%g
    ) primeG ))))))))).
Obligation 1.
  move=> [] [] [] [] [] [] [] [] [] [] []
    C1 C2 C3 C4 C5 C6 C8 C10 C11 C13 C14 C15.
  move=> [] [] [] [] [] [] [] [] [] [] [] [] [] []
    a b t r1 r2 r3 r4 r5 r6 r8 r10 r11 r13 r14 r15.
  move=> [] [] [] [] [] [] [] H [] H' [] H1 [] H2 [] H3.
  move=> [] H4 [] H5 H6 H8 H10 H11 H13 H14 H15. subst.
  repeat split; try done; try rewrite !Csimpl.
  + f_equal.
    * rewrite GRing.mulVr //.
      apply Z_is_unit_prime => //.
      apply /eqP. rewrite GRing.subr_eq0 eq_sym. by apply /eqP.
    * symmetry. by rewrite GRing.addrC GRing.subrK.
  + rewrite GRing.mulrC. f_equal.
    by rewrite GRing.addrC GRing.subrK.
  + f_equal.
    * rewrite exprSz expr1z exprSz expr1z.
      rewrite -!GRing.mulrA. f_equal.
      rewrite GRing.mulVr //.
      2: { apply Z_is_unit_prime => //. apply /eqP.
        rewrite GRing.subr_eq0 eq_sym. by apply /eqP. }
      by rewrite GRing.mulr1 GRing.mulrC.
    * symmetry. by rewrite GRing.addrC GRing.subrK.
  + f_equal. by rewrite GRing.addrC GRing.subrK.
  + f_equal.
    * rewrite exprSz expr1z -2!GRing.mulrA. f_equal.
      by rewrite GRing.mulrC.
    * symmetry. by rewrite GRing.addrC GRing.subrK.
  + f_equal. by rewrite GRing.addrA GRing.subrr GRing.add0r.
  + f_equal. by rewrite GRing.addrA GRing.subrr GRing.add0r.
Qed.
Obligation 2.
  move=> [] [] [] [] [] [] [] [] [] [] []
    C1 C2 C3 C4 C5 C6 C8 C10 C11 C13 C14 C15.
  move=> [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] []
    a b t x r1 r2 r3 r4 r5 r6 r8 r10 r10' r11 r13 r14 r15 r16 r17.
  move=> [] H1 [] H2 [] H3 [] H4 [] H5 [] H6 [] H8.
  move=> [] H10 [] H11 [] H13 [] H14 [] H15 [] H16 [] H17 H18. subst.
  destruct (b.1 - a.1 == 0)%B eqn:E; rewrite E. {
    move=> /eqP in E. rewrite E in H8.
    rewrite expgr0 Ch in H8. by symmetry. }
  assert (E' := E). move=> /eqP in E'.
  apply expgr_eq_l in H8; [| by apply Z_is_unit_prime ].
  apply expgr_eq_l in H11; [| by apply Z_is_unit_prime ].
  subst. rewrite !Csimpl in H16, H17.
  destruct (t.1 - (((b.2 - a.2) / (b.1 - a.1)) ^ 2 - a.1 - b.1) != 0)%B
    eqn:Ex; rewrite Ex. {
      simpl.
    apply (Ceq H16).
    assert (1 / (b.1 - a.1) * (b.2 - a.2) * (b.2 - a.2) / (b.1 - a.1)
      = (((b.2 - a.2) / (b.1 - a.1)) ^ 2)). {
      rewrite GRing.mul1r exprSz expr1z !GRing.mulrA.
      do 2 f_equal. by rewrite GRing.mulrC. }
    rewrite H. by apply /eqP.
  }
  destruct (t.2 - (((b.2 - a.2) / (b.1 - a.1)) * (b.1 - t.1) - a.2) != 0)%B
    eqn:Ey; rewrite Ey. { 
    apply (Ceq H17).
    rewrite GRing.mul1r (GRing.mulrC _ (b.2 - a.2)).
    by apply /eqP.
  }
  repeat split; try done; try rewrite !Csimpl; simpl.
  + rewrite GRing.subr_eq0 eq_sym in E. move=> /eqP // in E.
  + rewrite GRing.subr_eq0 in Ex. move=> /eqP in Ex.
    rewrite GRing.subr_eq0 in Ey. move=> /eqP in Ey.
    destruct a, b, t. simpl in Ex, Ey |- *. by subst.
  + by rewrite GRing.mul1r.
  + by rewrite GRing.mulrC GRing.mul1r.
  + f_equal.
    rewrite exprSz expr1z GRing.mul1r !GRing.mulrA.
    do 2 f_equal. by rewrite GRing.mulrC.
  + do 2 f_equal. by rewrite GRing.mulrC GRing.mul1r.
  + f_equal. by rewrite GRing.mul1r -GRing.mulrA GRing.mulrC.
Qed.
Obligation 3.
  move=> [] [] [] [] [] [] [] [] [] [] []
    C1 C2 C3 C4 C5 C6 C8 C10 C11 C13 C14 C15.
  move=> [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] []
    a b t x r1 r2 r3 r4 r5 r6 r8 r10 r10' r11 r13 r14 r15 r16 r17.
  split.
  + move=> [] H1 [] H2 [] H3 [] H4 [] H5 [] H6 [] H8.
    move=> [] H10 [] H11 [] H13 [] H14 [] H15 [] H16 [] H17 H18. subst.
    repeat (apply pair_equal_spec; split => //).
    * by rewrite H8 invMg mulgC mulKVg. 
    * rewrite H11. symmetry. by rewrite invMg mulgC mulKVg.
    * by rewrite /Com mulgC expgr1 mulKg.
    * by rewrite H16 -4!mulgA mulKg 2!mulKVg.
    * by rewrite -mulgA H17 -mulgA mulKg mulKVg.
  + move=> H. repeat apply pair_equal_spec in H as [H ?]. subst.
    repeat split; try done.
    * rewrite mulgC in H8.
      by apply mulg_eq_inv_r, mulg_eq_inv_l in H8.
    * apply esym in H6.
      apply mulg_eq_inv_l, mulg_eq_inv_r in H6.
      apply esym. by rewrite mulgC.
    * apply esym, mulg_eq_inv_r in H4.
      rewrite mulgC in H4. by apply esym.
    * by rewrite -H2 -4!mulgA 2!mulKg mulKVg.
    * rewrite -mulgA in H1.
      by rewrite -mulgA -H1 mulKg mulKVg.
Qed.

  (* (Old) Problem: *)
  (* ZKAttest Paper says C7 * C8 = ComTom(1) *)
  (* How should this be interpreted? *)

  (*
   * At this point, C8 = g ^ (b.1 - a.1)^-1 * h ^ r8,
   * or equivalently C8^(b.1 - a.1) = g * h ^ r8 * (b.1 - a.1).
   * This is almost provable by homomorphism, but it contains a product
     in h rather than in g, so we need a different commitment to b.1 - a.1.
     Is it sufficient to swap the generators in the commitment?
   *)
End ECAdd.
