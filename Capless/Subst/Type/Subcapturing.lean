import Capless.Subst.Basic
import Capless.Subcapturing

/-
Substitution theorems for type variable substitution in subcapturing judgments.
-/

namespace Capless

mutual

theorem CaptureKind.tsubst
  (h : CaptureKind Γ C K)
  (σ : TVarSubst Γ f Δ) :
  CaptureKind Δ C K :=
  match h with
  | .label hl =>
    have hl1 := σ.lmap _ _ hl
    .label hl1
  | .cvar hb =>
    have hb1 := σ.cmap _ _ hb
    .cvar hb1
  | .csub hsub hk =>
    have hsub1 := hsub.tsubst σ
    .csub hsub1 (hk.tsubst σ)
  | .sub hs hk =>
    .sub hs (hk.tsubst σ)
  | .empty => .empty
  | .proj hk => .proj $ hk.tsubst σ
  | .proj_kind => .proj_kind

theorem Subcapt.tsubst
  (h : Subcapt Γ C1 C2)
  (σ : TVarSubst Γ f Δ) :
  Subcapt Δ C1 C2 :=
  match h with
  | .trans ha hb => .trans (ha.tsubst σ) (hb.tsubst σ)
  | .subset hsub => .subset hsub
  | .union h1 h2 => .union (h1.tsubst σ) (h2.tsubst σ)
  | .var hb => by
    have ht := σ.map _ _ hb
    apply Subcapt.var <;> aesop
  | .cinstl hb =>
    have hb1 := σ.cmap _ _ hb
    .cinstl hb1
  | .cinstr hb =>
    have hb1 := σ.cmap _ _ hb
    .cinstr hb1
  | .cbound hb =>
    have hb1 := σ.cmap _ _ hb
    .cbound hb1
  | .proj hk => .proj $ hk.tsubst σ
  | .proj_sub hs => .proj_sub hs
  | .proj_l => .proj_l
  | .proj_r hs => .proj_r $ hs.tsubst σ
  | .proj_disj hd hk => .proj_disj hd $ hk.tsubst σ

end

end Capless
