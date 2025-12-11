import Capless.Subcapturing
import Capless.Renaming.Basic
import Mathlib.Data.Finset.Image

/-!
# Capture Variable Renaming for Subcapturing

This module proves that subcapturing relationships are preserved under capture variable
renaming. The main theorem `Subcapt.crename` shows that if `Γ ⊢ C1 <: C2`, then
after renaming capture variables with a valid renaming map, we have `Δ ⊢ C1.crename f <: C2.crename f`.
-/
namespace Capless

theorem CaptureSet.Subset.crename {C1 C2 : CaptureSet n k}
  (h : C1 ⊆ C2) :
  C1.crename f ⊆ C2.crename f := by
  induction h <;> try (solve | simp | constructor <;> try trivial)
  apply CaptureSet.Subset.union_rr; trivial

theorem CaptureKind.crename
  (h : CaptureKind Γ C K)
  (ρ : CVarMap Γ f Δ) :
  CaptureKind Δ (C.crename f) K := by
  induction h
  case var hb hk ih =>
    rw [CaptureSet.proj_crename] at ih
    apply! var (ρ.map _ _ hb) (ih _)
  case label hb => apply! label (ρ.lmap _ _ _ hb)
  case cvar hb => apply! cvar (ρ.cmap _ _ hb)
  case cbound hb hk ih =>
    rw [CaptureSet.proj_crename] at ih
    apply! cbound (ρ.cmap _ _ hb) (ih _)
  case cinstr hb hk ih =>
    rw [CaptureSet.proj_crename] at ih
    apply! cinstr (ρ.cmap _ _ hb) (ih _)
  case sub hs hk ih => apply! sub hs (ih _)
  case empty => apply empty
  case union ha hb => apply! union (ha _) (hb _)
  case absurd he => apply! absurd

theorem Subcapt.crename
  (h : Subcapt Γ C1 C2)
  (ρ : CVarMap Γ f Δ) :
  Subcapt Δ (C1.crename f) (C2.crename f) := by
  induction h <;> try rw [CaptureSet.proj_crename]
  case trans ha hb => apply! trans (ha _) (hb _)
  case subset hs => apply! subset $ hs.crename
  case union ha hb => apply! union (ha _) (hb _)
  case var hb => apply! var (ρ.map _ _ hb)
  case cinstl hb => apply! cinstl (ρ.cmap _ _ hb)
  case cinstr hb => apply! cinstr (ρ.cmap _ _ hb)
  case cbound hb => apply! cbound (ρ.cmap _ _ hb)
  case subkind hs => apply! subkind
  case proj_absurd => apply! proj_absurd
  case proj_split => apply! proj_split

end Capless
