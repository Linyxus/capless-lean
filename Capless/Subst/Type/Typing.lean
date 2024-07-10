import Capless.Subst.Basic
import Capless.Typing
namespace Capless

theorem Typed.tsubst
  (h : Typed Γ t E)
  (σ : TVarSubst Γ f Δ) :
  Typed Δ (t.trename f) (E.trename f) := by sorry

end Capless
