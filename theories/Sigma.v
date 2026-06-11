From SigmaZK Require Import Base.

Record sigma {Stmt Wit Forb Chal : finType}
  {R : Stmt → Wit → Prop} {E : Forb → Prop} :=
  { Rand : finType
  ; RandSim : finType
  ; Mes : finType
  ; Res : finType

  (* Algorithms *)
  ; commit : Stmt → Wit → Rand → Mes
  ; response : Stmt → Wit → Rand → Chal → Res
  ; verify : Stmt → Mes → Chal → Res → bool
  ; simulate : Stmt → Chal → RandSim → Mes * Res
  ; extractor : Stmt → Mes → Chal → Chal → Res → Res → Wit + Forb

  (* Properties *)
  ; complete : ∀ h w e r, 
      let a := commit h w r in
      let z := response h w r e in
      R h w → verify h a e z

  ; complete_sim : ∀ h e r, (* Required property for OR-constr. *)
      let (a, z) := simulate h e r in
      verify h a e z

  ; shvzk_fun : Wit → Chal → Rand → RandSim
  ; shvzk_inv : ∀ w e, inverse (shvzk_fun w e)
  ; shvzk : ∀ h w e r,
      let a := commit h w r in
      let z := response h w r e in
      let (a', z') := simulate h e (shvzk_fun w e r) in
      R h w → a = a' ∧ z = z'

  ; special_soundness : ∀ h a e z e' z',
      verify h a e z →
      verify h a e' z' →
      e != e' →
      case (R h) E (extractor h a e e' z z')
  }.

Arguments sigma {_} {_} {_} _ _ _.
