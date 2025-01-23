import Capybara.StaticSemantics
import Capybara.Morphism.Rebinding
namespace Capybara

theorem Subcapturing.rebind
  (h : Γ ⊢c C1 <: C2)
  (θ : Rebinding Γ Δ) :
  Δ ⊢c (C1.rename θ.ρ.asCapt) <: (C2.rename θ.ρ.asCapt) := by
  induction h
  case subset => sorry
  case trans ih1 ih2 => apply trans <;> aesop
  case union ih1 ih2 => apply union <;> aesop
  case mode => sorry
  case var => sorry
  case rovar => sorry
  case cvar_l => sorry
  case cvar_r => sorry

end Capybara
