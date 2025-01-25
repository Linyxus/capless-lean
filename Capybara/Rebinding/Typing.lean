import Capybara.StaticSemantics
import Capybara.Rebinding.Subtyping
namespace Capybara

theorem Typed.rebind {Γ : Context n m k} {Δ : Context n' m' k'}
  (h : Typed C Γ t E)
  (θ : Rebinding Γ Δ) :
  Typed (C.rename θ.ρ.asCapt) Δ (t.rename θ.ρ) (E.rename θ.ρ) := by
  induction h generalizing n' m' k' Δ
  case var =>
    sorry
  case pack =>
    sorry
  case subc =>
    sorry
  case abs =>
    sorry
  case tabs =>
    sorry
  case cabs =>
    sorry
  case fabs =>
    sorry
  case app =>
    sorry
  case tapp =>
    sorry
  case capp =>
    sorry
  case fapp =>
    sorry
  case letin =>
    sorry
  case unpack =>
    sorry

end Capybara
