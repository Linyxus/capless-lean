import Capless.Subtyping
import Capless.Subst.Basic
namespace Capless

theorem SSubtyp.csubst
  (h : SSubtyp Γ S1 S2)
  (σ : CVarSubst Γ f Δ) :
  SSubtyp Δ (S1.crename f) (S2.crename f) := sorry

end Capless
