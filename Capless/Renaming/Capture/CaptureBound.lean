import Capless.CaptureBound
import Capless.Renaming.Capture.Subcapturing

/-!
# Capture Variable Renaming for Capture Bounding

This module proves that capture bound relationships are preserved under capture variable
renaming. The main theorem `Subcapt.crename` shows that subcapturing judgments
remain valid when capture variables are renamed consistently between contexts.
-/
namespace Capless

theorem CaptureKind.crename
  (h : CaptureKind Γ C K)
  (ρ : CVarMap Γ f Δ) :
  CaptureKind Δ (C.crename f) K := by
  induction h
  case var hb hk ih =>
    simp [CaptureSet.crename_singleton]
    apply var
    have hb1 := ρ.map _ _ hb
    simp [EType.crename, CType.crename] at hb1
    exact hb1
    apply ih ρ
  case cvar hc =>
    apply cvar
    exact ρ.cmap _ _ hc
  case sub hs hk ih =>
    apply sub hs
    apply ih ρ
  case csub hs hk ih =>
    have hs1 := hs.crename ρ
    apply csub hs1
    apply ih ρ
  case union hc1 hc2 ih1 ih2 =>
    apply union <;> aesop
  case empty => apply empty

theorem CaptureBound.crename
  (h : CaptureBound Γ C B)
  (ρ : CVarMap Γ f Δ) :
  CaptureBound Δ (C.crename f) (B.crename f) := by
  cases h
  case subcapt hs =>
    apply subcapt
    apply Subcapt.crename hs ρ
  case subkind hk =>
    apply subkind
    apply CaptureKind.crename hk ρ

end Capless
