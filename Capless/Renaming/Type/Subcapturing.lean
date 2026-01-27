import Capless.Subcapturing
import Capless.Renaming.Basic
import Mathlib.Data.Finset.Image

/-!
# Type Variable Renaming for Subcapturing

This module proves that subcapturing relationships are preserved under type variable
renaming. The main theorem `Subcapt.trename` shows that subcapturing judgments
remain valid when type variables are renamed consistently between contexts.
-/
namespace Capless

theorem ReachSet.trename
  {Γ : Context n m k} {Δ : Context n m' k}
  (h : ReachSet Γ C R)
  (ρ : TVarMap Γ f Δ) :
  ReachSet Δ C R := by
  induction h generalizing m'
  case empty => constructor
  case union ih1 ih2 => apply union (ih1 ρ) (ih2 ρ)
  case var hb hr ih =>
    have hb1 := ρ.map _ _ hb
    apply var hb1
    exact ih ρ
  case cinstr hb hr ih =>
    have hb1 := ρ.cmap _ _ hb
    apply cinstr hb1
    exact ih ρ
  case cbound hb hr ih =>
    have hb1 := ρ.cmap _ _ hb
    apply cbound hb1
    exact ih ρ
  case ckind hb =>
    have hb1 := ρ.cmap _ _ hb
    apply ckind hb1
  case label hb =>
    have hb1 := ρ.lmap _ _ _ hb
    apply label hb1
  case absurd he => apply! absurd
  case var_reach ih => apply! var_reach $ ih _
  case cvar_creach ih => apply! cvar_creach $ ih _

theorem CaptureKind.trename
  (h : CaptureKind Γ C K)
  (ρ : TVarMap Γ f Δ) :
  CaptureKind Δ C K := by
  induction h
  case var hb hk ih => apply! var (ρ.map _ _ hb) (ih _)
  case label hb => apply! label (ρ.lmap _ _ _ hb)
  case cvar hb => apply! cvar (ρ.cmap _ _ hb)
  case cbound hb hk ih => apply! cbound (ρ.cmap _ _ hb) (ih _)
  case cinstr hb hk ih => apply! cinstr (ρ.cmap _ _ hb) (ih _)
  case sub hs hk ih => apply! sub hs (ih _)
  case empty => apply empty
  case union ha hb => apply! union (ha _) (hb _)
  case singleton_absurd => apply! singleton_absurd
  case reach ih => apply! reach $ ih _

theorem Subcapt.trename
  (h : Subcapt Γ C1 C2)
  (ρ : TVarMap Γ f Δ) :
  Subcapt Δ C1 C2 := by
  induction h
  case trans ha hb => apply! trans (ha _) (hb _)
  case subset hs => apply! subset
  case union ha hb => apply! union (ha _) (hb _)
  case var hb => apply! var (ρ.map _ _ hb)
  case cinstl hb => apply! cinstl (ρ.cmap _ _ hb)
  case cinstr hb => apply! cinstr (ρ.cmap _ _ hb)
  case cbound hb => apply! cbound (ρ.cmap _ _ hb)
  case proj_r hk => apply! proj_r (hk.trename _)
  case reachsetl hr => apply! reachsetl $ hr.trename _
  case reachsetr hr => apply! reachsetr $ hr.trename _

end Capless
