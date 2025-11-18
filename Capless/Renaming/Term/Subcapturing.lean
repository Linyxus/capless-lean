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
  apply CaptureSet.Subset.union_rr; trivial

mutual
theorem CaptureKind.rename
  (h : Γ ⊢ C :k K)
  (ρ : VarMap Γ f Δ) : Δ ⊢ (C.rename f) :k K :=
  match h with
  | .empty => .empty
  | .label hl => .label (ρ.lmap _ _ hl)
  | .cvar hb => .cvar (ρ.cmap _ _ hb)
  | .csub hs hk => .csub (hs.rename ρ) (hk.rename ρ)
  | .sub hs hk => .sub hs (hk.rename ρ)
  | .proj_kind => by
    rw [← CaptureSet.proj_rename_comm]
    apply CaptureKind.proj_kind
  | .proj hk => by
    rw [← CaptureSet.proj_rename_comm]
    apply CaptureKind.proj (hk.rename ρ)

theorem Subcapt.rename
  (h : Subcapt Γ C1 C2)
  (ρ : VarMap Γ f Δ) :
  Subcapt Δ (C1.rename f) (C2.rename f) :=
  match h with
  | .trans ha hb => .trans (ha.rename ρ) (hb.rename ρ)
  | .subset hs => by
    apply Subcapt.subset
    apply CaptureSet.Subset.rename hs
  | .union ha hb => .union (ha.rename ρ) (hb.rename ρ)
  | .var hb => .var (ρ.map _ _ hb)
  | .cinstl hb => .cinstl (ρ.cmap _ _ hb)
  | .cinstr hb => .cinstr (ρ.cmap _ _ hb)
  | .cbound hb => .cbound (ρ.cmap _ _ hb)
  | .proj h1 => by
    repeat rw [← CaptureSet.proj_rename_comm]
    apply Subcapt.proj (h1.rename ρ)
  | .proj_sub hs => by
    repeat rw [← CaptureSet.proj_rename_comm]
    apply Subcapt.proj_sub hs
  | .proj_l => by
    rw [← CaptureSet.proj_rename_comm]
    apply Subcapt.proj_l
  | .proj_r hk => by
    rw [← CaptureSet.proj_rename_comm]
    apply Subcapt.proj_r (hk.rename ρ)
  | .proj_disj hd hk => by
    rw [← CaptureSet.proj_rename_comm]
    apply Subcapt.proj_disj hd (hk.rename ρ)
end

end Capless
