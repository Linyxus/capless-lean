import Capless.Subst.Basic
import Capless.Subcapturing
import Capless.Typing.Basic
import Capless.Renaming.Term.Subcapturing

/-
Substitution theorems for term variable substitution in subcapturing judgments.
-/

namespace Capless

mutual
theorem CaptureKind.subst
  (h : CaptureKind Γ C K)
  (σ : VarSubst Γ f Δ) :
  CaptureKind Δ (C.rename f) K :=
  match h with
  | .label hl =>
    have hl1 := σ.lmap _ _ hl
    .label hl1
  | .cvar hb => by
    have hb1 := σ.cmap _ _ hb
    simp [CBinding.rename, CBound.rename] at hb1
    apply CaptureKind.cvar hb1
  | .csub hsub hk =>
    have hsub1 := hsub.subst σ
    .csub hsub1 (hk.subst σ)
  | .sub hs hk => .sub hs (hk.subst σ)
  | .empty => .empty
  | .proj_kind => by
    simp
    apply CaptureKind.proj_kind
  | .proj hk => by
    simp
    apply CaptureKind.proj $ hk.subst σ


theorem Subcapt.subst
  (h : Subcapt Γ C1 C2)
  (σ : VarSubst Γ f Δ) :
  Subcapt Δ (C1.rename f) (C2.rename f) :=
  match h with
  | .trans ha hb => .trans (ha.subst σ) (hb.subst σ)
  | .subset hsub => by
    apply Subcapt.subset
    apply CaptureSet.Subset.rename hsub
  | .union h1 h2 => by
    have ih1 := h1.subst σ
    have ih2 := h2.subst σ
    rw [CaptureSet.rename_union]
    apply Subcapt.union <;> trivial
  | .var hb => by
    have ht := σ.map _ _ hb
    simp [CType.rename] at ht
    have h := Typing.inv_subcapt ht
    trivial
  | .cinstl hb =>
    have hb1 := σ.cmap _ _ hb
    .cinstl hb1
  | .cinstr hb =>
    have hb1 := σ.cmap _ _ hb
    .cinstr hb1
  | .cbound hb => by
    have hb1 := σ.cmap _ _ hb
    simp [CBinding.rename, CBound.rename] at hb1
    apply Subcapt.cbound hb1
  | .proj h1 => by
    simp
    apply Subcapt.proj (h1.subst σ)
  | .proj_sub hs => by
    simp
    apply Subcapt.proj_sub hs
  | .proj_l => by
    simp
    apply Subcapt.proj_l
  | .proj_r hk => by
    simp
    apply Subcapt.proj_r (hk.subst σ)
  | .proj_disj hd hk => by
    simp
    apply Subcapt.proj_disj hd (hk.subst σ)
end

end Capless
