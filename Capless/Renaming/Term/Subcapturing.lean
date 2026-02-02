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

theorem ReachSet.rename
  {Γ : Context n m k} {Δ : Context n' m k}
  (h : ReachSet Γ C R)
  (ρ : VarMap Γ f Δ) :
  ReachSet Δ (C.rename f) (R.rename f) := by
  induction h generalizing n'
  case empty => constructor
  case union ih1 ih2 => apply union (ih1 ρ) (ih2 ρ)
  case var hb hr ih =>
    have hb1 := ρ.map _ _ hb
    simp [CType.rename] at hb1
    apply var hb1
    rw [← CaptureSet.proj_rename]; exact ih ρ
  case cinstr hb hr ih =>
    have hb1 := ρ.cmap _ _ hb
    simp [CBinding.rename] at hb1
    apply cinstr hb1
    rw [← CaptureSet.proj_rename]; exact ih ρ
  case cbound hb hr ih =>
    have hb1 := ρ.cmap _ _ hb
    simp [CBinding.rename] at hb1
    apply cbound hb1
    rw [← CaptureSet.proj_rename]; exact ih ρ
  case ckind hb =>
    have hb1 := ρ.cmap _ _ hb
    simp [CBinding.rename] at hb1
    apply ckind hb1
  case label hb =>
    have hb1 := ρ.lmap _ _ _ hb
    apply label hb1
  case absurd he => apply! absurd
  case var_reach ih => apply! var_reach $ ih _
  case cvar_creach ih => apply! cvar_creach $ ih _

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
  case reach ih =>
  rw [CaptureSet.reach_rename]
  apply! reach $ ih _

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
  case reachsetl hr =>
    rw [CaptureSet.reach_rename]
    apply! reachsetl $ hr.rename _
  case reachsetr hr =>
    rw [CaptureSet.reach_rename]
    apply! reachsetr $ hr.rename _

end Capless
