import Capless.Subcapturing
import Capless.Renaming.Basic
import Mathlib.Data.Finset.Image
namespace Capless

theorem CaptureSet.Subset.crename {C1 C2 : CaptureSet n k}
  (h : C1 ⊆ C2) :
  C1.crename f ⊆ C2.crename f := by
  induction h <;> try (solve | simp | constructor <;> try trivial)
  apply CaptureSet.Subset.union_rr; trivial

theorem Subcapt.crename
  (h : Subcapt Γ C1 C2)
  (ρ : CVarMap Γ f Δ) :
  Subcapt Δ (C1.crename f) (C2.crename f) := by
  induction h
  case trans ih1 ih2 => apply trans <;> aesop
  case subset hsub =>
    apply subset
    apply CaptureSet.Subset.crename; trivial
  case union ih1 ih2 =>
    simp [CaptureSet.crename_union]
    apply union <;> aesop
  case var hb =>
    simp [CaptureSet.crename_singleton]
    apply var
    have hb1 := ρ.map _ _ hb
    simp [EType.crename, CType.crename] at hb1
    assumption
  case cinstl hb =>
    simp [CaptureSet.crename_csingleton]
    have hb1 := ρ.cmap _ _ hb
    simp [CBinding.rename] at hb1
    apply cinstl
    assumption
  case cinstr hb =>
    simp [CaptureSet.crename_csingleton]
    have hb1 := ρ.cmap _ _ hb
    simp [CBinding.rename] at hb1
    apply cinstr
    assumption

end Capless
