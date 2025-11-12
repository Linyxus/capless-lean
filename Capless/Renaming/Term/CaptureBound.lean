import Capless.CaptureBound
import Capless.Renaming.Term.Subcapturing

/-!
# Variable Renaming for Capture Bounding

This module proves that capture bound relationships are preserved under variable
renaming. The main theorem `Subcapt.rename` shows that subcapturing judgments
remain valid when variables are renamed consistently between contexts.
-/
namespace Capless

theorem CaptureKind.rename
  (h : CaptureKind Γ C K)
  (ρ : VarMap Γ f Δ) :
  CaptureKind Δ (C.rename f) K := by
  induction h
  case var hb hk ih =>
    apply var
    have hb1 := ρ.map _ _ hb
    simp [EType.crename, CType.crename] at hb1
    exact hb1
    apply ih ρ
  case label hl =>
    apply label
    have hl1 := ρ.lmap _ _ hl
    exact hl1
  case cvar hc =>
    apply cvar
    exact ρ.cmap _ _ hc
  case sub hs hk ih =>
    apply sub hs
    apply ih ρ
  case csub hs hk ih =>
    have hs1 := hs.rename ρ
    apply csub hs1
    apply ih ρ
  case union hc1 hc2 ih1 ih2 =>
    apply union <;> aesop
  case empty => apply empty

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
