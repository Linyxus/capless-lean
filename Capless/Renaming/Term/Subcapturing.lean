import Capless.Subcapturing
import Capless.Renaming.Basic
import Mathlib.Data.Finset.Image

/-!
# Term Variable Renaming for Subcapturing

This module proves that subcapturing relationships are preserved under term variable
renaming. The main theorem `Subcapt.rename` shows that if `Γ ⊢ C1 <: C2`, then
after renaming term variables with a valid renaming map, we have `Δ ⊢ C1.rename f <: C2.rename f`.
-/

namespace Capless

theorem CaptureSet.Subset.rename {C1 C2 : CaptureSet n k}
  (h : C1 ⊆ C2) :
  C1.rename f ⊆ C2.rename f := by
  induction h <;> try (solve | simp | constructor <;> try trivial)
  apply! union_rr
  apply! proj_merge

theorem CaptureKind.rename
  (h : Γ ⊢ C :k K)
  (ρ : VarMap Γ f Δ) : Δ ⊢ (C.rename f) :k K := by
  induction h
  case var hb hk ih =>
    rw [CaptureSet.proj_rename] at ih
    apply! var (ρ.map _ _ hb) (ih _)
  case label hb => apply! label (ρ.lmap _ _ _ hb)
  case cvar hb => apply! cvar (ρ.cmap _ _ hb)
  case cbound hb hk ih =>
    rw [CaptureSet.proj_rename] at ih
    apply! cbound (ρ.cmap _ _ hb) (ih _)
  case cinstr hb hk ih =>
    rw [CaptureSet.proj_rename] at ih
    apply! cinstr (ρ.cmap _ _ hb) (ih _)
  case sub hs hk ih => apply! sub hs (ih _)
  case empty => apply empty
  case union ha hb => apply! union (ha _) (hb _)
  case singleton_absurd => apply! singleton_absurd

theorem Subcapt.rename
  (h : Subcapt Γ C1 C2)
  (ρ : VarMap Γ f Δ) :
  Subcapt Δ (C1.rename f) (C2.rename f) :=by
  induction h <;> try rw [CaptureSet.proj_rename]
  case trans ha hb => apply! trans (ha _) (hb _)
  case subset hs => apply! subset $ hs.rename
  case union ha hb => apply! union (ha _) (hb _)
  case var hb => apply! var (ρ.map _ _ hb)
  case cinstl hb => apply! cinstl (ρ.cmap _ _ hb)
  case cinstr hb => apply! cinstr (ρ.cmap _ _ hb)
  case cbound hb => apply! cbound (ρ.cmap _ _ hb)
  case proj_r hk => apply! proj_r (hk.rename _)

end Capless
