import Capless.Subcapturing
import Capless.Renaming.Basic
import Mathlib.Data.Finset.Image
namespace Capless

theorem Subcapt.rename
  (h : Subcapt Γ C1 C2)
  (ρ : VarMap Γ f Δ) :
  Subcapt Δ (C1.rename f) (C2.rename f) := by
  induction h
  case trans ih1 ih2 => apply trans <;> aesop
  case subset hsub =>
    apply subset
    rename_i D1 D2 _
    cases D1; cases D2
    cases hsub; simp at *
    constructor <;> simp [CaptureSet.rename] <;>
      try (solve | apply Finset.image_subset_image; assumption | assumption)
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

end Capless
