import Capless.Subcapturing
import Capless.Subst.Basic

/-
Substitution theorems for capture variable substitution in subcapturing judgments.
-/

namespace Capless

theorem CaptureKind.csubst
  (h : CaptureKind Γ C K)
  (σ : CVarSubst Γ f Δ) :
  CaptureKind Δ (C.crename f) K := by
  induction h
  case var hb hk ih =>
    rewrite [CaptureSet.proj_crename] at ih
    apply! var (σ.map _ _ hb) (ih _)
  case label hb => apply label (σ.lmap _ _ _ hb)
  case cvar hb =>
    cases σ.cmap_bound _ _ hb
    apply! apply_proj_singleton
  case cbound hb hk ih =>
    rewrite [CaptureSet.proj_crename] at ih
    cases σ.cmap_bound _ _ hb
    rename_i hb
    apply subcapt _ hb.apply_proj_singleton
    apply! ih
  case cinstr hb hk ih =>
    rewrite [CaptureSet.proj_crename] at ih
    apply! cinstr (σ.cmap _ _ hb) (ih _)
  case sub hs hk ih =>
    apply! sub hs (ih _)
  case empty => apply empty
  case singleton_absurd => apply! singleton_absurd
  case union ha hb => apply! union (ha _) (hb _)

theorem Subcapt.csubst
  (h : Subcapt Γ C1 C2)
  (σ : CVarSubst Γ f Δ) :
  Subcapt Δ (C1.crename f) (C2.crename f) := by
  induction h <;> try rw [CaptureSet.proj_crename]
  case trans ha hb => apply! trans (ha _) (hb _)
  case subset hs => apply subset (CaptureSet.Subset.crename hs)
  case union ha hb => apply! union (ha _) (hb _)
  case var hb => apply var (σ.map _ _ hb)
  case cinstl hb => apply cinstl (σ.cmap _ _ hb)
  case cinstr hb => apply cinstr (σ.cmap _ _ hb)
  case cbound hb =>
    cases σ.cmap_bound _ _ hb
    apply! apply_proj_singleton
  case proj_r hk => apply! proj_r (hk.csubst _)

end Capless
