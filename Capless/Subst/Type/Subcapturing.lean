import Capless.Subst.Basic
import Capless.Subcapturing

/-
Substitution theorems for type variable substitution in subcapturing judgments.
-/

namespace Capless


theorem CaptureKind.tsubst
  (h : CaptureKind Γ C K)
  (σ : TVarSubst Γ f Δ) :
  CaptureKind Δ C K := by
  induction h
  case var hb hk ih =>
    apply! var (σ.map _ _ hb) (ih _)
  case label hb => apply label (σ.lmap _ _ _ hb)
  case cvar hb => apply cvar (σ.cmap _ _ hb)
  case cbound hb hk ih => apply! cbound (σ.cmap _ _ hb) (ih _)
  case cinstr hb hk ih => apply! cinstr (σ.cmap _ _ hb) (ih _)
  case sub hs hk ih => apply! sub hs (ih _)
  case empty => apply empty
  case singleton_absurd => apply! singleton_absurd
  case union ha hb => apply! union (ha _) (hb _)

theorem Subcapt.tsubst
  (h : Subcapt Γ C1 C2)
  (σ : TVarSubst Γ f Δ) :
  Subcapt Δ C1 C2 := by
  induction h
  case trans ha hb => apply! trans (ha _) (hb _)
  case subset hs => apply subset hs
  case union ha hb => apply! union (ha _) (hb _)
  case var hb => apply var (σ.map _ _ hb)
  case cinstl hb => apply cinstl (σ.cmap _ _ hb)
  case cinstr hb => apply cinstr (σ.cmap _ _ hb)
  case cbound hb => apply cbound (σ.cmap _ _ hb)
  case absurd hk he => apply! absurd (hk.tsubst _)

end Capless
