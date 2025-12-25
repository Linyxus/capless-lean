import Capless.Subcapturing
import Capless.Renaming.Basic
import Mathlib.Data.Finset.Image

/-!
# Type Variable Renaming for Subcapturing

This module proves that subcapturing relationships are preserved under type variable
renaming. The main theorem `Subcapt.trename` shows that subcapturing judgments
remain valid when type variables are renamed consistently between contexts.
-/
namespace Capless

theorem CaptureKind.trename
  (h : CaptureKind Γ C K)
  (ρ : TVarMap Γ f Δ) :
  CaptureKind Δ C K := by
  induction h
  case var hb hk ih => apply! var (ρ.map _ _ hb) (ih _)
  case label hb => apply! label (ρ.lmap _ _ _ hb)
  case cvar hb => apply! cvar (ρ.cmap _ _ hb)
  case cbound hb hk ih => apply! cbound (ρ.cmap _ _ hb) (ih _)
  case cinstr hb hk ih => apply! cinstr (ρ.cmap _ _ hb) (ih _)
  case sub hs hk ih => apply! sub hs (ih _)
  case empty => apply empty
  case union ha hb => apply! union (ha _) (hb _)
  case singleton_absurd => apply! singleton_absurd

theorem Subcapt.trename
  (h : Subcapt Γ C1 C2)
  (ρ : TVarMap Γ f Δ) :
  Subcapt Δ C1 C2 := by
  induction h
  case trans ha hb => apply! trans (ha _) (hb _)
  case subset hs => apply! subset
  case union ha hb => apply! union (ha _) (hb _)
  case var hb => apply! var (ρ.map _ _ hb)
  case cinstl hb => apply! cinstl (ρ.cmap _ _ hb)
  case cinstr hb => apply! cinstr (ρ.cmap _ _ hb)
  case cbound hb => apply! cbound (ρ.cmap _ _ hb)
  case proj_r hk => apply! proj_r (hk.trename _)

end Capless
