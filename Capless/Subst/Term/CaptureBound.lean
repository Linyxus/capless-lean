import Capless.CaptureBound
import Capless.Subst.Basic
import Capless.Subst.Term.Subcapturing

/-
Substitution theorems for term variable substitution in capture kind judgments.
-/

namespace Capless

theorem CaptureKind.subst
  (h : CaptureKind Γ C K)
  (σ : VarSubst Γ f Δ) :
  CaptureKind Δ (C.rename f) K := by
  induction h
  case var hb hk ih =>
    have hb1 := σ.map _ _ hb
    simp [EType.rename, CType.rename] at hb1
    have h := Typing.inv_subcapt hb1
    apply csub h (ih σ)
  case label hl =>
    have hl1 := σ.lmap _ _ hl
    apply label hl1
  case cvar hb =>
    have hb1 := σ.cmap _ _ hb
    apply cvar hb1
  case csub hsub hk ih =>
    have hsub1 := hsub.subst σ
    apply csub hsub1 (ih σ)
  case sub hs hk ih =>
    apply sub hs (ih σ)
  case union h1 h2 ih1 ih2 =>
    apply union (ih1 σ) (ih2 σ)
  case empty =>
    apply empty

theorem CaptureBound.subst
  (h : CaptureBound Γ C B)
  (σ: VarSubst Γ f Δ) :
  CaptureBound Δ (C.rename f) (B.rename f) := by
    cases h <;> constructor
    apply Subcapt.subst _ σ ; assumption
    apply CaptureKind.subst _ σ ; assumption

end Capless
