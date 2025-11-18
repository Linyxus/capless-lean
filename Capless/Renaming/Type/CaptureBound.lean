import Capless.CaptureBound
import Capless.Renaming.Type.Subcapturing

/-!
# Type Variable Renaming for Capture Bounding

This module proves that capture bound relationships are preserved under type variable
renaming. The main theorem `Subcapt.trename` shows that subcapturing judgments
remain valid when type variables are renamed consistently between contexts.
-/
namespace Capless

theorem CaptureBound.trename
  (h : CaptureBound Γ C B)
  (ρ : TVarMap Γ f Δ) :
  CaptureBound Δ C B := by
  cases h
  case subcapt hs =>
    apply subcapt
    apply Subcapt.trename hs ρ
  case subkind hk =>
    apply subkind
    apply CaptureKind.trename hk ρ

end Capless
