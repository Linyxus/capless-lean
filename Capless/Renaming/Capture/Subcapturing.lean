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
  case proj_union =>
    simp
    apply proj_union
  case union_proj =>
    simp
    apply union_proj

mutual

theorem CaptureKind.crename
  (h : CaptureKind Γ C K)
  (ρ : CVarMap Γ f Δ) :
  CaptureKind Δ (C.crename f) K :=
  match h with
  | .label hl =>
    have hl1 := ρ.lmap _ _ hl
    CaptureKind.label hl1
  | .cvar hc =>
    CaptureKind.cvar (ρ.cmap _ _ hc)
  | .sub hs hk => CaptureKind.sub hs (hk.crename ρ)
  | .csub hs hk => by
    have hk1 := hk.crename ρ
    have hs1 := hs.crename ρ
    apply CaptureKind.csub hs1
    apply hk1
  | .empty => CaptureKind.empty
  | .proj_kind => by
    simp
    apply CaptureKind.proj_kind
  | .proj hk => by
    simp
    apply CaptureKind.proj
    apply hk.crename ρ

theorem Subcapt.crename
  (h : Subcapt Γ C1 C2)
  (ρ : CVarMap Γ f Δ) :
  Subcapt Δ (C1.crename f) (C2.crename f) :=
  match h with
  | .trans a b => by
    apply Subcapt.trans (a.crename ρ) (b.crename ρ)
  | .subset hsub => by
    apply Subcapt.subset
    apply CaptureSet.crename_monotone hsub
  | .union a b => by
    simp
    apply Subcapt.union (a.crename ρ) (b.crename ρ)
  | .var hb => by
    have hb1 := ρ.map _ _ hb
    simp [CType.crename] at hb1
    apply Subcapt.var hb1
  | .cinstl hb => by
    have hb1 := ρ.cmap _ _ hb
    apply Subcapt.cinstl hb1
  | .cinstr hb => by
    have hb1 := ρ.cmap _ _ hb
    apply Subcapt.cinstr hb1
  | .cbound hb => by
    have hb1 := ρ.cmap _ _ hb
    apply Subcapt.cbound hb1
  | .proj hs => by
    simp
    apply Subcapt.proj
    apply hs.crename ρ
  | .proj_sub hs => by
    simp
    apply Subcapt.proj_sub hs
  | .proj_l => by
    simp
    apply Subcapt.proj_l
  | .proj_r hk => by
    simp
    apply Subcapt.proj_r
    apply hk.crename ρ
  | .proj_disj hd hk => by
    simp
    apply Subcapt.proj_disj hd
    apply hk.crename ρ

end

end Capless
