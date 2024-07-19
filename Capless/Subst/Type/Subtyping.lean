import Capless.Subst.Basic
import Capless.Subtyping
import Capless.Subst.Type.Subcapturing
namespace Capless

theorem SSubtyp.tsubst
  (h : SSubtyp Γ S1 S2)
  (σ : TVarSubst Γ f Δ) :
  SSubtyp Δ (S1.trename f) (S2.trename f) := sorry

theorem CSubtyp.tsubst
  (h : CSubtyp Γ S1 S2)
  (σ : TVarSubst Γ f Δ) :
  CSubtyp Δ (S1.trename f) (S2.trename f) := by
  cases h
  case capt hc hs =>
    simp [CType.trename]
    apply CSubtyp.capt
    { apply! Subcapt.tsubst }
    { apply! SSubtyp.tsubst }

theorem ESubtyp.tsubst
  (h : ESubtyp Γ S1 S2)
  (σ : TVarSubst Γ f Δ) :
  ESubtyp Δ (S1.trename f) (S2.trename f) := sorry

theorem ESubtyp.tnarrow
  (h : ESubtyp (Γ.tvar (TBinding.bound S)) E1 E2)
  (hs : SSubtyp Γ S' S) :
  ESubtyp (Γ.tvar (TBinding.bound S')) E1 E2 := by
  rw [<- EType.trename_id (E := E1), <- EType.trename_id (E := E2)]
  apply? ESubtyp.tsubst
  { apply? TVarSubst.narrow }

end Capless
