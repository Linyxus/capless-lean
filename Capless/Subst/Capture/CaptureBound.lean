import Capless.CaptureBound
import Capless.Subst.Basic
import Capless.Subst.Capture.Subcapturing

/-
Substitution theorems for capture variable substitution in capture kind judgments.
-/

namespace Capless

theorem CaptureBound.csubst
  (h : CaptureBound Γ C B)
  (σ: CVarSubst Γ f Δ) :
  CaptureBound Δ (C.crename f) (B.crename f) := by
    cases h <;> constructor
    apply Subcapt.csubst _ σ ; assumption
    apply CaptureKind.csubst _ σ ; assumption

end Capless
