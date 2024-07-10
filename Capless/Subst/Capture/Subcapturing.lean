import Capless.Subcapturing
import Capless.Subst.Basic
namespace Capless

theorem Subcapt.csubst
  (h : Subcapt Γ C1 C2)
  (σ : CVarSubst Γ f Δ) :
  Subcapt Δ (C1.crename f) (C2.crename f) := by sorry

end Capless
