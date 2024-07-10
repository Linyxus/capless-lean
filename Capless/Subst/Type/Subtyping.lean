import Capless.Subst.Basic
import Capless.Subtyping
namespace Capless

theorem SSubtyp.tsubst
  (h : SSubtyp Γ S1 S2)
  (σ : TVarSubst Γ f Δ) :
  SSubtyp Δ (S1.trename f) (S2.trename f) := sorry

end Capless
