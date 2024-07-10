import Capless.Typing
import Capless.Subst.Basic
namespace Capless

theorem Typed.subst
  (h : Typed Γ t E)
  (σ : VarSubst Γ f Δ) :
  Typed Δ (t.rename f) (E.rename f) := sorry

end Capless
