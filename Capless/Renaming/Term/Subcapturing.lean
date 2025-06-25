import Capless.Subcapturing
import Capless.Renaming.Basic
import Mathlib.Data.Finset.Image

/-!
# Term Variable Renaming for Subcapturing

This module proves that subcapturing relationships are preserved under term variable
renaming. The main theorem `Subcapt.rename` shows that if `Γ ⊢ C1 <: C2`, then
after renaming term variables with a valid renaming map, we have `Δ ⊢ C1.rename f <: C2.rename f`.
-/

namespace Capless

theorem CaptureSet.Subset.rename {C1 C2 : CaptureSet n k}
  (h : C1 ⊆ C2) :
  C1.rename f ⊆ C2.rename f := by
  induction h <;> try (solve | simp | constructor <;> try trivial)
  apply CaptureSet.Subset.union_rr; trivial

theorem Subcapt.rename
  (h : Subcapt Γ C1 C2)
  (ρ : VarMap Γ f Δ) :
  Subcapt Δ (C1.rename f) (C2.rename f) := by
  induction h
  case trans ih1 ih2 => apply trans <;> aesop
  case subset hsub =>
    apply subset
    apply CaptureSet.Subset.rename; trivial
  case union ih1 ih2 =>
    simp [CaptureSet.rename_union]
    apply union <;> aesop
  case var hb =>
    simp [CaptureSet.rename_singleton]
    apply var
    have hb1 := ρ.map _ _ hb
    simp [EType.rename, CType.rename] at hb1
    assumption
  case cinstl hb =>
    simp [CaptureSet.rename_csingleton]
    have hb1 := ρ.cmap _ _ hb
    simp [CBinding.rename] at hb1
    apply cinstl
    assumption
  case cinstr hb =>
    simp [CaptureSet.rename_csingleton]
    have hb1 := ρ.cmap _ _ hb
    simp [CBinding.rename] at hb1
    apply cinstr
    assumption
  case cbound hb =>
    simp [CaptureSet.rename_csingleton]
    have hb1 := ρ.cmap _ _ hb
    simp [CBinding.rename, CBound.rename] at hb1
    apply cbound
    easy

end Capless
