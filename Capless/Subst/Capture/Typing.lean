import Capless.Subtyping
import Capless.Subst.Basic
namespace Capless

theorem Typed.csubst
  (h : Typed Γ t E)
  (σ : CVarSubst Γ f Δ) :
  Typed Δ (t.crename f) (E.crename f) := by sorry

theorem Typed.copen
  (h : Typed (Γ.cvar CBinding.bound) t E) :
  Typed Γ (t.copen c) (E.copen c) := by sorry

end Capless
