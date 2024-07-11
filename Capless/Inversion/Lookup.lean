import Capless.Store
import Capless.Renaming.Term.Typing
import Capless.Renaming.Type.Typing
import Capless.Renaming.Capture.Typing
import Capless.Inversion.Context
namespace Capless

def Store.lookup_inv_typing
  (hl : Store.Bound σ x v)
  (ht : TypedStore σ Γ)
  (hb : Context.Bound Γ x T) :
  Typed Γ v (EType.type T) := by
  induction ht
  case empty => cases hb
  case val ih =>
    cases hl
    case here =>
      cases hb
      rename_i E _ ht _ _
      have ht1 := ht.weaken (T := E)
      simp [EType.weaken, EType.rename, CType.weaken] at *
      exact ht1
    case there_val  =>
      have ⟨T1, hb1, heq⟩ := Context.var_bound_succ_inv hb
      subst heq
      rename_i hl _
      have ih := ih hl hb1
      rename_i E _ _ _ _ _ _ _
      have ih := ih.weaken (T := E)
      simp [EType.weaken, EType.rename, CType.weaken] at *
      exact ih
  case tval S _ ih =>
    cases hb; cases hl
    rename_i hb _ hl
    have ih := ih hl hb
    have ih := ih.tweaken (b := TBinding.inst S)
    simp [EType.tweaken, EType.trename, CType.tweaken] at *
    exact ih
  case cval C _ ih =>
    cases hb; cases hl
    rename_i hb _ hl
    have ih := ih hl hb
    have ih := ih.cweaken (b := CBinding.inst C)
    simp [EType.cweaken, EType.crename, CType.cweaken] at *
    exact ih

end Capless
