import Capless.Subst.Basic
import Capless.Subcapturing
import Capless.Typing.Basic
import Capless.Renaming.Term.Subcapturing

/-
Substitution theorems for term variable substitution in subcapturing judgments.
-/

namespace Capless

theorem CaptureKind.subst
  (h : CaptureKind Γ C K)
  (σ : VarSubst Γ f Δ) :
  CaptureKind Δ (C.rename f) K := by
  induction h
  case var hb hk ih =>
    rewrite [CaptureSet.proj_rename] at ih
    have h1 := Typing.inv_subcapt $ σ.map _ _ hb
    apply subcapt $ ih σ
    apply h1.apply_proj_singleton
  case label hb => apply label (σ.lmap _ _ _ hb)
  case cvar hb => apply cvar (σ.cmap _ _ hb)
  case cbound hb hk ih =>
    rewrite [CaptureSet.proj_rename] at ih
    apply! cbound (σ.cmap _ _ hb) (ih _)
  case cinstr hb hk ih =>
    rewrite [CaptureSet.proj_rename] at ih
    apply! cinstr (σ.cmap _ _ hb) (ih _)
  case sub hs hk ih =>
    apply! sub hs (ih _)
  case empty => apply empty
  case absurd he => apply! absurd
  case union ha hb => apply! union (ha _) (hb _)

theorem Subcapt.subst
  (h : Subcapt Γ C1 C2)
  (σ : VarSubst Γ f Δ) :
  Subcapt Δ (C1.rename f) (C2.rename f) := by
  induction h <;> try rw [CaptureSet.proj_rename]
  case trans ha hb => apply! trans (ha _) (hb _)
  case subset hs => apply subset (CaptureSet.Subset.rename hs)
  case union ha hb => apply! union (ha _) (hb _)
  case var hb =>
    have h1 := Typing.inv_subcapt (σ.map _ _ hb)
    apply h1.apply_proj_singleton
  case cinstl hb => apply cinstl (σ.cmap _ _ hb)
  case cinstr hb => apply cinstr (σ.cmap _ _ hb)
  case cbound hb => apply cbound (σ.cmap _ _ hb)
  case subkind hs => apply! subkind
  case proj_absurd => apply! proj_absurd
  case proj_split => apply! proj_split

end Capless
