import Capless.Subtyping
import Capless.Subst.Basic
namespace Capless

theorem Typed.csubst
  (h : Typed Γ t E)
  (σ : CVarSubst Γ f Δ) :
  Typed Δ (t.crename f) (E.crename f) := by sorry

end Capless
