import Capless.Subcapturing
import Capless.Subst.Basic

/-
Substitution theorems for capture variable substitution in subcapturing judgments.
-/

namespace Capless

mutual
theorem CaptureKind.csubst
  (h : CaptureKind Γ C K)
  (σ : CVarSubst Γ f Δ) :
  CaptureKind Δ (C.crename f) K :=
  match h with
  | .label hl =>
    have hl1 := σ.lmap _ _ hl
    .label hl1
  | .cvar hb => by
    cases σ.cmap_bound _ _ hb
    assumption
  | .csub hsub hk =>
    have hsub1 := hsub.csubst σ
    .csub hsub1 (hk.csubst σ)
  | .sub hs hk => .sub hs (hk.csubst σ)
  | .empty => .empty
  | .proj_kind => by
    rw [← CaptureSet.proj_crename_comm]
    apply CaptureKind.proj_kind
  | .proj hk => by
    rw [← CaptureSet.proj_crename_comm]
    apply CaptureKind.proj $ hk.csubst σ


theorem Subcapt.csubst
  (h : Subcapt Γ C1 C2)
  (σ : CVarSubst Γ f Δ) :
  Subcapt Δ (C1.crename f) (C2.crename f) :=
  match h with
  | .trans ha hb => .trans (ha.csubst σ) (hb.csubst σ)
  | .subset hsub => by
    apply Subcapt.subset
    apply (CaptureSet.crename_monotone hsub)
  | .union h1 h2 => by
    have ih1 := h1.csubst σ
    have ih2 := h2.csubst σ
    rw [CaptureSet.crename_union]
    apply Subcapt.union <;> trivial
  | .var hb =>
    have ht := σ.map _ _ hb
    Subcapt.var ht
  | .cinstl hb =>
    have hb1 := σ.cmap _ _ hb
    .cinstl hb1
  | .cinstr hb =>
    have hb1 := σ.cmap _ _ hb
    .cinstr hb1
  | .cbound hb => by
    have hb1 := σ.cmap_bound _ _ hb
    cases hb1
    easy
  | .proj h1 => by
    repeat rw [← CaptureSet.proj_crename_comm]
    apply Subcapt.proj (h1.csubst σ)
  | .proj_sub hs => by
    repeat rw [← CaptureSet.proj_crename_comm]
    apply Subcapt.proj_sub hs
  | .proj_l => by
    rw [← CaptureSet.proj_crename_comm]
    apply Subcapt.proj_l
  | .proj_r hk => by
    rw [← CaptureSet.proj_crename_comm]
    apply Subcapt.proj_r (hk.csubst σ)
  | .proj_disj hd hk => by
    rw [← CaptureSet.proj_crename_comm]
    apply Subcapt.proj_disj hd (hk.csubst σ)
end

end Capless
