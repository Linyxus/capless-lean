import Capless.Subst.Basic
import Capless.Subcapturing
namespace Capless

theorem Subcapt.tsubst
  (h : Subcapt Γ C1 C2)
  (σ : TVarSubst Γ f Δ) :
  Subcapt Δ C1 C2 := by
  induction h
  case trans => apply trans <;> aesop
  case subset hsub =>
    apply subset; easy
  case union h1 h2 =>
    apply union <;> aesop
  case var hb =>
    have ht := σ.map _ _ hb
    simp [EType.trename, CType.trename] at ht
    apply var <;> aesop
  case cinstl hb =>
    have hb1 := σ.cmap _ _ hb
    apply cinstl; easy
  case cinstr hb =>
    have hb1 := σ.cmap _ _ hb
    apply cinstr; easy
  case cbound hb =>
    have hb1 := σ.cmap _ _ hb
    apply cbound; easy

end Capless
