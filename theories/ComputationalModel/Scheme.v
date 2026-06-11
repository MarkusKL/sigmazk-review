From SigmaZK Require Import Base.

From extructures Require Import ord fset fmap.
From mathcomp Require Import reals distr realsum.
From SSProve.Crypt Require Import NominalPrelude.
Import PackageNotation. #[local] Open Scope package_scope.


Section Scheme.

Record sigma :=
  { Stmt : choice_type
  ; Wit : choice_type
  ; Mes : choice_type
  ; State : choice_type
  ; Chal : choice_type
  ; Res : choice_type

  ; R : Stmt → Wit → bool

  ; commit :
    ∀ (h : Stmt) (w : Wit),
      code emptym [interface] (Mes × State)

  ; response :
    ∀ (h : Stmt) (w : Wit)
      (a : Mes) (s : State) (e : Chal),
      code emptym [interface] Res

  ; verify :
    ∀ (h : Stmt) (a : Mes) (e : Chal)
      (z : Res),
      bool

  ; simulate :
    ∀ (h : Stmt) (e : Chal),
      code emptym [interface] (Mes × Res)

  ; extractor :
    ∀ (h : Stmt) (a : Mes)
      (e : Chal) (e' : Chal)
      (z : Res) (z' : Res),
      'option Wit
  }.


(* Section: Completeness *)

Definition Input p : choice_type
  := p.(Stmt) × p.(Wit) × p.(Chal).

Definition RUN : nat := 1.

Definition IComplete p :=
  [interface [ RUN ] : { Input p ~> bool } ].

Definition Complete_real p :
  game (IComplete p) :=
  [package emptym ;
    [ RUN ] '(h, w, e) {
      #assert p.(R) h w ;;
      '(a, s) ← p.(commit) h w ;;
      z ← p.(response) h w a s e ;;
      ret (p.(verify) h a e z)
    }
  ].

Definition Complete_ideal p :
  game (IComplete p) :=
  [package emptym ;
    [ RUN ] '(h, w, e) {
      #assert p.(R) h w ;;
      ret true
    }
  ].

Definition Complete p b :=
  if b then Complete_real p else Complete_ideal p.


(* Section: SHVZK *)

Definition TRANSCRIPT : nat := 0.

Definition ITranscript p := 
  [interface [ TRANSCRIPT ] : { Input p ~> p.(Mes) × p.(Res) } ].

Definition SHVZK_real p :
  game (ITranscript p) :=
  [package emptym ;
    [ TRANSCRIPT ] '(h, w, e) {
      #assert p.(R) h w ;;
      '(a, s) ← p.(commit) h w ;;
      z ← p.(response) h w a s e ;;
      ret (a, z)
    }
  ].

Definition SHVZK_ideal p :
  game (ITranscript p) :=
  [package emptym ;
    [ TRANSCRIPT ] '(h, w, e) {
      #assert p.(R) h w ;;
      '(a, z) ← p.(simulate) h e ;;
      ret (a, z)
    }
  ].

Definition SHVZK p b :=
  if b then SHVZK_real p else SHVZK_ideal p.


(* Section: Relating SHVZK and correctness *)

Definition Verify_call p :
  package (ITranscript p) (IComplete p) :=
  [package emptym ;
    [ RUN ] '(h, w, e) {
      '(a, z) ← call [ TRANSCRIPT ] (h, w, e) ;;
      ret (p.(verify) h a e z)
    }
  ].

Lemma Verify_SHVZK_Complete_perf p
  : perfect (IComplete p) (Verify_call p ∘ SHVZK_real p) (Complete_real p).
Proof.
  ssprove_share.
  eapply prove_perfect.
  eapply eq_rel_perf_ind_eq.
  simplify_eq_rel hwe.
  ssprove_code_simpl.
  destruct hwe as [[h w] e].
  ssprove_code_simpl_more.
  ssprove_sync_eq => _.
  ssprove_code_simpl.
  eapply rsame_head => as'.
  move: as' => [a s].
  eapply rsame_head => z.
  eapply r_ret; auto.
Qed.

Definition Complete_sim p := (Verify_call p ∘ SHVZK_ideal p)%sep.

Lemma Adv_Complete_sim p A
  `{ValidPackage (loc A) (IComplete p) A_export A} :
  (Adv (Complete_sim p) (Complete_ideal p) A
    <= AdvOf (SHVZK p) (A ∘ Verify_call p) + AdvOf (Complete p) A)%R.
Proof.
  ssprove_hop (Verify_call p ∘ SHVZK_real p)%sep.
  apply Num.Theory.lerD.
  + rewrite Adv_reduction Adv_sym //.
  + ssprove_hop (Complete_real p).
    rewrite Verify_SHVZK_Complete_perf.
    rewrite GRing.add0r //.
Qed.

(* Section: 2-special-soundness *)

Definition SOUNDNESS : nat := 4.

Definition Opening p := p.(Chal) × p.(Res).
Definition Soundness p :=
  p.(Stmt) × p.(Mes) × Opening p × Opening p.

Definition ISoundness p :=
  [interface [ SOUNDNESS ] : { Soundness p ~> 'bool } ].

Definition Special_Soundness p b : game (ISoundness p) :=
  [package emptym ;
    [ SOUNDNESS ] '(h, a, (e, z), (e', z')) {
      let v1 := p.(verify) h a e z in
      let v2 := p.(verify) h a e' z' in
      let v3 := e != e' in
      ret [==> v1, v2, v3, b =>
        if p.(extractor) h a e e' z z' is Some w then p.(R) h w else false
      ]
    }
  ].

End Scheme.
