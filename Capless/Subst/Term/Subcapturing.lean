import Capless.Subst.Basic
import Capless.Subcapturing
import Capless.Typing.Basic
import Capless.Renaming.Term.Subcapturing
namespace Capless

theorem Subcapt.subst
  (h : Subcapt Γ C1 C2)
  (σ : VarSubst Γ f Δ) :
  Subcapt Δ (C1.rename f) (C2.rename f) := by
  induction h
  case trans => apply trans <;> aesop
  case subset hsub =>
    apply subset
    apply! CaptureSet.Subset.rename
  case union h1 h2 =>
    simp [CaptureSet.rename_union]
    apply union <;> aesop
  case var hb =>
    have ht := σ.map _ _ hb
    simp [EType.rename, CType.rename] at ht
    have h := Typing.inv_subcapt ht
    simp [CaptureSet.rename_singleton]; trivial
  case cinstl hb =>
    have hb1 := σ.cmap _ _ hb
    simp [CaptureSet.rename_csingleton]
    apply cinstl
    simp [CBinding.rename] at hb1
    trivial
  case cinstr hb =>
    have hb1 := σ.cmap _ _ hb
    simp [CaptureSet.rename_csingleton]
    apply cinstr
    simp [CBinding.rename] at hb1
    trivial

end Capless
