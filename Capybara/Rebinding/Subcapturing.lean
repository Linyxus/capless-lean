import Capybara.StaticSemantics
import Capybara.Morphism.Rebinding
namespace Capybara

theorem Subcapturing.rebind
  (h : Γ ⊢c C1 <: C2)
  (θ : Rebinding Γ Δ) :
  Δ ⊢c (C1.rename θ.ρ.asCapt) <: (C2.rename θ.ρ.asCapt) := by
  induction h
  case subset hs =>
    apply Subcapturing.subset
    apply CaptureSet.rename_subset hs
  case trans ih1 ih2 =>
    apply Subcapturing.trans
    · exact ih1 θ
    · exact ih2 θ
  case union ih1 ih2 =>
    apply Subcapturing.union
    · exact ih1 θ
    · exact ih2 θ
  case mode h1 h2 =>
    simp [CaptureSet.qualified_rename]
    apply mode; easy
  case var hb =>
    simp [CaptureSet.rename]
    simp [CaptureSet.qualified_rename]
    apply var
    have hb1 := θ.var hb
    exact hb1
  case rovar hb =>
    simp [CaptureSet.rename]
    simp [CaptureSet.qualified_rename]
    apply rovar
    have hb1 := θ.var hb
    exact hb1
  case cvar_l hb =>
    simp [CaptureSet.rename]
    simp [CaptureSet.qualified_rename]
    apply cvar_l
    have hb1 := θ.cvar hb
    exact hb1
  case cvar_r hb =>
    simp [CaptureSet.rename]
    simp [CaptureSet.qualified_rename]
    apply cvar_r
    have hb1 := θ.cvar hb
    exact hb1

end Capybara
