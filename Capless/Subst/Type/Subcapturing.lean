import Capless.Subst.Basic
import Capless.Subcapturing
namespace Capless

theorem Subcapt.tsubst
  (h : Subcapt Γ C1 C2)
  (σ : TVarSubst Γ f Δ) :
  Subcapt Δ C1 C2 := by sorry

end Capless
