import Capybara.Morphism.Rebinding
import Capybara.StaticSemantics
import Capybara.Rebinding.CaptureRoot
namespace Capybara

theorem RootChaining.rebind
  (h : RootChaining Γ r1 r2)
  (θ : Rebinding Γ Δ) :
  RootChaining Δ (r1.rename θ.ρ.cvar) (r2.rename θ.ρ.cvar) := by
  cases h
  case c_rw => apply c_rw
  case c_drop hc =>
    apply c_drop
    have hc' := θ.cvar hc
    easy
    sorry

/-!
Rebinding preserves the chaining of capture sets.
-/
theorem Chaining.rebind
  (h : Chaining Γ C1 C2)
  (θ : Rebinding Γ Δ) :
  Chaining Δ (C1.rename θ.ρ.asCapt) (C2.rename θ.ρ.asCapt) := by
  sorry

end Capybara
