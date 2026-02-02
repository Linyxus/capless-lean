import Capless.CaptureBound
import Capless.Subst.Basic
import Capless.Subst.Type.Subcapturing

/-
Substitution theorems for type variable substitution in capture kind judgments.
-/

namespace Capless

theorem CaptureBound.tsubst
  (h : CaptureBound Γ C B)
  (σ: TVarSubst Γ f Δ) :
  CaptureBound Δ C B := by
    cases h <;> constructor
    apply Subcapt.tsubst _ σ ; assumption
    apply CaptureKind.tsubst _ σ ; assumption

end Capless
