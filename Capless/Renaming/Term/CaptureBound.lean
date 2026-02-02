import Capless.CaptureBound
import Capless.Renaming.Term.Subcapturing

/-!
# Variable Renaming for Capture Bounding

This module proves that capture bound relationships are preserved under variable
renaming. The main theorem `Subcapt.rename` shows that subcapturing judgments
remain valid when variables are renamed consistently between contexts.
-/
namespace Capless

theorem CaptureBound.rename
  (h : CaptureBound Γ C B)
  (ρ : VarMap Γ f Δ) :
  CaptureBound Δ (C.rename f) (B.rename f) := by
  cases h
  case subcapt hs =>
    apply subcapt
    apply Subcapt.rename hs ρ
  case subkind hk =>
    apply subkind
    apply CaptureKind.rename hk ρ

end Capless
