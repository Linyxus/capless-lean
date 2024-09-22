import Capless.Store
import Capless.Renaming.Term.Typing
import Capless.Renaming.Type.Typing
import Capless.Renaming.Capture.Typing
import Capless.Inversion.Context
import Capless.Inversion.Typing
namespace Capless

def Store.lookup_inv_bound
  (hl : Store.Bound σ x v)
  (ht : TypedStore σ Γ)
  (hb : Context.Bound Γ x T) :
  ∃ Cv, Typed Γ v (EType.type T) Cv := by
  induction ht
  case empty => cases hb
  case val ih =>
    cases hl
    case here =>
      cases hb
      rename_i E _ _ ht _ _
      have ht1 := ht.weaken (T := E)
      simp [EType.weaken, EType.rename, CType.weaken] at *
      constructor; exact ht1
    case there_val  =>
      have ⟨T1, hb1, heq⟩ := Context.var_bound_succ_inv hb
      subst heq
      rename_i hl _
      have ⟨Cv0, ih⟩ := ih hl hb1
      rename_i E _ _ _ _ _ _ _ _
      have ih := ih.weaken (T := E)
      simp [EType.weaken, EType.rename, CType.weaken] at *
      constructor; exact ih
  case tval S _ ih =>
    cases hb; cases hl
    rename_i hb _ hl
    have ⟨Cv0, ih⟩ := ih hl hb
    have ih := ih.tweaken (b := TBinding.inst S)
    simp [EType.tweaken, EType.trename, CType.tweaken] at *
    constructor; exact ih
  case cval C _ ih =>
    cases hb; cases hl
    rename_i hb _ hl
    have ⟨Cv0, ih⟩ := ih hl hb
    have ih := ih.cweaken (b := CBinding.inst C)
    simp [EType.cweaken, EType.crename, CType.cweaken] at *
    constructor; exact ih

theorem Store.lookup_inv_typing
  (hl : Store.Bound σ x v)
  (ht : TypedStore σ Γ)
  (hx : Typed Γ (Term.var x) (EType.type (CType.capt C S)) Cx) :
  ∃ Cv Cv0, Typed Γ v (EType.type (CType.capt Cv S)) Cv0 := by
  have ⟨C0, S0, hb, hsub⟩ := Typed.var_inv hx
  have ⟨Cv0, hv⟩ := Store.lookup_inv_bound hl ht hb
  cases hsub
  rename_i hsc hss
  constructor; constructor
  apply Typed.sub
  exact hv; apply Subcapt.refl
  constructor
  constructor
  apply Subcapt.refl
  trivial

end Capless
