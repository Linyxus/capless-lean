import Capless.Subcapturing
import Capless.Subst.Basic
namespace Capless

theorem CaptureSet.crename_monotone {C1 C2 : CaptureSet n k} {f : FinFun k k'} -- TODO move
  (h : C1 ⊆ C2) :
  C1.crename f ⊆ C2.crename f := by
    cases h
    cases C1; cases C2
    simp at *
    constructor
    trivial
    apply Finset.image_subset_image
    trivial

theorem CaptureSet.cweaken_monotone {C1 C2 : CaptureSet n k} -- TODO move
  (h : C1 ⊆ C2) :
  C1.cweaken ⊆ C2.cweaken := by
    simp [CaptureSet.cweaken]
    apply CaptureSet.crename_monotone
    trivial

theorem Subcapt.csubst
  (h : Subcapt Γ C1 C2)
  (σ : CVarSubst Γ f Δ) :
  Subcapt Δ (C1.crename f) (C2.crename f) := by
  induction h
  case trans => apply trans <;> aesop
  case subset hsub =>
    apply subset
    apply (CaptureSet.crename_monotone hsub)
  case union h1 h2 =>
    have ih1 := h1 σ
    have ih2 := h2 σ
    rw [CaptureSet.crename_union]
    apply union <;> trivial
  case var hb =>
    have ht := σ.map _ _ hb
    simp [EType.crename, CType.crename] at ht
    apply var <;> aesop
  case cinstl hb =>
    have hb1 := σ.cmap _ _ hb
    apply cinstl
    trivial
  case cinstr hb =>
    have hb1 := σ.cmap _ _ hb
    apply cinstr
    trivial


end Capless
