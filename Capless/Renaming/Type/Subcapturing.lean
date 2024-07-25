import Capless.Subcapturing
import Capless.Renaming.Basic
import Mathlib.Data.Finset.Image
namespace Capless

theorem Subcapt.trename
  (h : Subcapt Γ C1 C2)
  (ρ : TVarMap Γ f Δ) :
  Subcapt Δ C1 C2 := by
  induction h
  case trans ih1 ih2 => apply trans <;> aesop
  case subset hs =>
    apply subset
    trivial
  case union ih1 ih2 =>
    apply union <;> aesop
  case var hb =>
    apply var
    have hb1 := ρ.map _ _ hb
    simp [EType.trename, CType.trename] at hb1
    exact hb1
  case cinstl hb =>
    apply cinstl
    have hb1 := ρ.cmap _ _ hb
    exact hb1
  case cinstr hb =>
    apply cinstr
    have hb1 := ρ.cmap _ _ hb
    exact hb1

end Capless
