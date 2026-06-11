From SigmaZK Require Import Base Groups Sigma DepHom Pedersen.

(* Common instantiations of protocols *)

Program Definition Pedersen_expg {Stat Wit Forb Chal : finType} {G : finGroupType}
  {R : Stat → Wit → Prop} {Err : Forb → Prop} (g : G) (f : Wit → G)
  (geng : generator [set: G] g) (primeG : prime #|G|)
  (P : sigma Chal (λ '(h, B) '(w, r), R h w ∧ B = f w * g ^ r) Err)
  : sigma Chal R Err := Pedersen (λ w r, f w * g ^ r) _ P.
Obligation 1.
  intros. apply inv_comp; [ apply inv_mulg | apply inv_expg => // ]; by apply prime_gt1.
Qed.


Fixpoint expG (T : finGroupType) (n : nat) : finGroupType
  := match n with
     | 0 => 'I_1
     | 1 => T
     | n.+1 => expG T n * T
     end.

Notation " T ^ n " := (expG T n) : type_scope.


Class ElemOrder (G : finGroupType) (n : nat) :=
  elem_order :  ∀ x : G, x ^+ n = 1.

Lemma eq_elem_order {G : finGroupType} {n} : #|G| = n → ElemOrder G n.
Proof. move=> H x. by rewrite -H expg_card. Qed.

#[export] Hint Extern 5 (ElemOrder _ _) =>
  by apply eq_elem_order : typeclass_instances.

Lemma mulg_prod [G1 G2 : finGroupType] (g1 g1' : G1) (g2 g2' : G2)
  : (g1, g2) * (g1', g2') = (g1 * g1', g2 * g2').
Proof. done. Qed.

Lemma expg_prod [G1 G2 : finGroupType] (g1 : G1) (g2 : G2) (n : nat)
  : (g1, g2) ^+ n = (g1 ^+ n, g2 ^+ n).
Proof.
  induction n => //.
  rewrite 3!expgS IHn mulg_prod //.
Qed.

#[export] Instance prod_elem_order {G G' n} :
  ElemOrder G n → ElemOrder G' n → ElemOrder (G * G') n.
Proof. move=> H H' [x x']. by rewrite expg_prod H H'. Qed.

#[export] Instance expG_elem_order {G m n} :
  ElemOrder G n → ElemOrder (G ^ m) n.
Proof.
  move=> H x. destruct m.
  { destruct (fintype1 (card_ord 1)) as [y E]. by rewrite 2!E. }
  induction m; [ by rewrite H | by apply prod_elem_order ].
Qed.

Program Definition DepHomPrime {Forb : finType} {Err : Forb → Prop}
  {G H : finGroupType} {I : finType} q P (F : I → G → H)
  (Hprime : prime q) `{HF : ∀ i, Hom (F i)} `{HE : ElemOrder H q}
  : sigma 'Z_q (λ h w, P h = F h w) Err :=
    DepHom q (λ _, 1) F P _ _ _.
Obligation 1. intros. apply gcdz_prime_diff_Z => //. Qed.
Obligation 2. intros. by rewrite Hom1 HE. Qed.
