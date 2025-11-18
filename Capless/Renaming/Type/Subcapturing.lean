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

mutual


theorem CaptureKind.trename
  (h : CaptureKind Γ C K)
  (ρ : TVarMap Γ f Δ) :
  CaptureKind Δ C K :=
  match h with
  | .label hl => .label (ρ.lmap _ _ hl)
  | .cvar hb => .cvar (ρ.cmap _ _ hb)
  | .csub hs hk => .csub (hs.trename ρ) (hk.trename ρ)
  | .sub hs hk => .sub hs (hk.trename ρ)
  | .empty => .empty
  | .proj_kind => .proj_kind
  | .proj hk => .proj (hk.trename ρ)

theorem Subcapt.trename
  (h : Subcapt Γ C1 C2)
  (ρ : TVarMap Γ f Δ) :
  Subcapt Δ C1 C2 :=
  match h with
  | .trans ha hb => .trans (ha.trename ρ) (hb.trename ρ)
  | .subset hs => .subset hs
  | .union ha hb => .union (ha.trename ρ) (hb.trename ρ)
  | .var hb => .var (ρ.map _ _ hb)
  | .cinstl hb => .cinstl (ρ.cmap _ _ hb)
  | .cinstr hb => .cinstr (ρ.cmap _ _ hb)
  | .cbound hb => .cbound (ρ.cmap _ _ hb)
  | .proj h1 => .proj (h1.trename ρ)
  | .proj_sub hs => .proj_sub hs
  | .proj_l => .proj_l
  | .proj_r hk => .proj_r (hk.trename ρ)
  | .proj_disj hd hk => .proj_disj hd (hk.trename ρ)
end

end Capless
