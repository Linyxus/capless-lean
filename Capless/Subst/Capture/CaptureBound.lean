import Capless.CaptureBound
import Capless.Subst.Basic
import Capless.Subst.Capture.Subcapturing

/-
Substitution theorems for capture variable substitution in capture kind judgments.
-/

namespace Capless

theorem CaptureKind.csubst
  (h : CaptureKind Γ C K)
  (σ : CVarSubst Γ f Δ) :
  CaptureKind Δ (C.crename f) K := by
  induction h
  case var hb hk ih =>
    have hb1 := σ.map _ _ hb
    apply CaptureKind.var hb1 (ih σ)
  case cvar hb =>
    cases σ.cmap_bound _ _ hb
    assumption
  case csub hsub hk ih =>
    have hsub1 := hsub.csubst σ
    apply csub hsub1 (ih σ)
  case sub hs hk ih =>
    apply sub hs (ih σ)
  case union h1 h2 ih1 ih2 =>
    apply union (ih1 σ) (ih2 σ)
  case empty =>
    apply empty

theorem CaptureBound.csubst
  (h : CaptureBound Γ C B)
  (σ: CVarSubst Γ f Δ) :
  CaptureBound Δ (C.crename f) (B.crename f) := by
    cases h <;> constructor
    apply Subcapt.csubst _ σ ; assumption
    apply CaptureKind.csubst _ σ ; assumption

end Capless
