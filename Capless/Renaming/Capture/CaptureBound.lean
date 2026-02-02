import Capless.CaptureBound
import Capless.Renaming.Capture.Subcapturing

/-!
# Capture Variable Renaming for Capture Bounding

This module proves that capture bound relationships are preserved under capture variable
renaming. The main theorem `Subcapt.crename` shows that subcapturing judgments
remain valid when capture variables are renamed consistently between contexts.
-/
namespace Capless

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
