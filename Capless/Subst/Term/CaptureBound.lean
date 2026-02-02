import Capless.CaptureBound
import Capless.Subst.Basic
import Capless.Subst.Term.Subcapturing

/-
Substitution theorems for term variable substitution in capture kind judgments.
-/

namespace Capless

theorem CaptureBound.subst
  (h : CaptureBound Γ C B)
  (σ: VarSubst Γ f Δ) :
  CaptureBound Δ (C.rename f) (B.rename f) := by
    cases h <;> constructor
    apply Subcapt.subst _ σ ; assumption
    apply CaptureKind.subst _ σ ; assumption

end Capless
