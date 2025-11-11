import Capless.CaptureBound
import Capless.Renaming.Type.Subcapturing

/-!
# Type Variable Renaming for Capture Bounding

This module proves that capture bound relationships are preserved under type variable
renaming. The main theorem `Subcapt.trename` shows that subcapturing judgments
remain valid when type variables are renamed consistently between contexts.
-/
namespace Capless

theorem CaptureKind.trename
  (h : CaptureKind Γ C K)
  (ρ : TVarMap Γ f Δ) :
  CaptureKind Δ C K := by
  induction h
  case var hb hk ih =>
    apply var
    have hb1 := ρ.map _ _ hb
    simp [EType.trename, CType.trename] at hb1
    exact hb1
    apply ih ρ
  case cvar hc =>
    apply cvar
    exact ρ.cmap _ _ hc
  case sub hs hk ih =>
    apply sub hs
    apply ih ρ
  case union hc1 hc2 ih1 ih2 =>
    apply union <;> aesop
  case empty => apply empty


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
