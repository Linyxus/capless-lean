import Capless.Subst.Basic
import Capless.Typing
namespace Capless

theorem Typed.tsubst
  (h : Typed Γ t E)
  (σ : TVarSubst Γ f Δ) :
  Typed Δ (t.trename f) (E.trename f) := by sorry

theorem Typed.tnarrow
  (h : Typed (Γ.tvar (TBinding.bound S)) t E)
  (hs : SSubtyp Γ S' S) :
  Typed (Γ.tvar (TBinding.bound S')) t E := by
  rw [<- Term.trename_id (t := t), <- EType.trename_id (E := E)]
  apply? Typed.tsubst
  apply? TVarSubst.narrow

end Capless
