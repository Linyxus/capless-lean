import Capless.CaptureBound
import Capless.Subst.Basic
import Capless.Subst.Type.Subcapturing

/-
Substitution theorems for type variable substitution in capture kind judgments.
-/

namespace Capless

theorem CaptureKind.tsubst
  (h : CaptureKind Γ C K)
  (σ : TVarSubst Γ f Δ) :
  CaptureKind Δ C K := by
  induction h
  case var hb hk ih =>
    have hb1 := σ.map _ _ hb
    simp [CType.trename] at hb1
    apply var hb1 (ih σ)
  case cvar hb =>
    have hb1 := σ.cmap _ _ hb
    apply cvar hb1
  case csub hsub hk ih =>
    have hsub1 := hsub.tsubst σ
    apply csub hsub1 (ih σ)
  case sub hs hk ih =>
    apply sub hs (ih σ)
  case union h1 h2 ih1 ih2 =>
    apply union (ih1 σ) (ih2 σ)
  case empty =>
    apply empty

theorem CaptureBound.tsubst
  (h : CaptureBound Γ C B)
  (σ: TVarSubst Γ f Δ) :
  CaptureBound Δ C B := by
    cases h <;> constructor
    apply Subcapt.tsubst _ σ ; assumption
    apply CaptureKind.tsubst _ σ ; assumption

end Capless
