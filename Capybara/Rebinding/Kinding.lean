import Capybara.Morphism.Rebinding
import Capybara.StaticSemantics
import Capybara.Rebinding.CaptureRoot
import Capybara.Rebinding.Separation
namespace Capybara

/-!
Rebinding preserves the kinding of capture sets.
-/
theorem Kinding.rebind
  (h : Kinding Γ C K)
  (θ : Rebinding Γ Δ) :
  Kinding Δ (C.rename θ.ρ.asCapt) (K.rename θ.ρ.asCapt) := by
  cases h
  case fresh hk =>
    apply fresh
    apply ForallRoot.rebind
      (P := λ r => FreshRoot Γ r)
      (Q := λ r => FreshRoot Δ r)
      (θ := θ)
      (h := hk)
    intros r hf
    apply hf.rebind
  case sep_imm hs hk =>
    apply sep_imm
    apply Separation.rebind
      (h := hs)
      (θ := θ)
    apply ForallRoot.rebind
      (P := λ r => RORoot Γ r)
      (Q := λ r => RORoot Δ r)
      (θ := θ)
      (h := hk)
    intros r hr
    apply hr.rebind
  case sep_mut hs hk =>
    apply sep_mut
    apply Separation.rebind
      (h := hs)
      (θ := θ)
    apply ForallRoot.rebind
      (P := λ r => MutRoot Γ r)
      (Q := λ r => MutRoot Δ r)
      (θ := θ)
      (h := hk)
    intros r hr
    apply hr.rebind

end Capybara
