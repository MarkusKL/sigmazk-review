From Coq Require Export Utf8.

#[export] Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-prefix".
From mathcomp Require Export all_ssreflect all_algebra.

(* Enforce sensible proof structure. *)
#[export] Set Bullet Behavior "Strict Subproofs".
#[export] Set Default Goal Selector "!".
#[export] Set Primitive Projections.

(* Modify behavior of Program tactic. *)
#[export] Unset Program Cases.
#[export] Obligation Tactic := move=> //=.

#[global] Bind Scope type_scope with finType.


(* Basic definitions *)

Definition case {A B C} (f : A → C) (g : B → C) := λ v,
  match v with
  | inl a => f a
  | inr b => g b
  end.

Definition NoErr := λ _ : void, False.


(* Type exponentiation *)

Fixpoint expt (T : Type) (n : nat) : Type
  := match n with
     | 0 => unit
     | 1 => T
     | n.+1 => expt T n * T
     end.

Notation " T ^ n " := (expt T n) : type_scope.


(* Inverses *)

Open Scope type_scope.

Definition inverse [S T : Type] (f : S → T) :=
  { inv | cancel f inv * cancel inv f }.

Definition inv_fun [S T] {f} (f' : @inverse S T f) :=
  projT1 f'.

Coercion inv_fun : inverse >-> Funclass.

Definition inv_rew [S T] {f} (f' : @inverse S T f)
  : cancel f f' * cancel f' f := projT2 f'.

Lemma inv_id {T} : inverse (@id T).
Proof. by exists id. Qed.

Lemma inv_comp {T T' T''} (f : T' → T'') (g : T → T')
  : inverse f → inverse g → inverse (f \o g).
Proof.
  intros f' g'.
  exists (g' \o f'); split => x.
  - by rewrite /= (inv_rew f') (inv_rew g').
  - by rewrite /= (inv_rew g') (inv_rew f').
Qed.

Lemma inv_prod {T T' S S'} (f : T → T') (g : S → S')
  : inverse f → inverse g → inverse (λ '(x1, x2), (f x1, g x2)).
Proof.
  intros f' g'.
  exists (λ '(y1, y2), (f' y1, g' y2)); split => [[x1 x2]|[x1 x2]].
  - by rewrite /= (inv_rew f') (inv_rew g').
  - by rewrite /= (inv_rew g') (inv_rew f').
Qed.

Lemma inv_dep {T T' S S'} (f : S → T → T') (g : S → S')
  : (∀ x, inverse (f x)) → inverse g → inverse (λ '(x1, x2), (f x2 x1, g x2)).
Proof.
  intros f' g'.
  exists (λ '(y1, y2), (f' (g' y2) y1, g' y2)); split => [[x1 x2]|[x1 x2]].
  - by rewrite /= (inv_rew g') (inv_rew (f' _)).
  - by rewrite /= (inv_rew g') (inv_rew (f' _)).
Qed.
