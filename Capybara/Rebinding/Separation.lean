import Capybara.Morphism.Rebinding
import Capybara.StaticSemantics
import Capybara.Rebinding.CaptureRoot
namespace Capybara

/-!
This file proves that rebinding preserves separation checking.
-/

theorem RootSeparation.rebind
  (h : RootSeparation Γ r1 r2)
  (θ : Rebinding Γ Δ) :
  RootSeparation Δ (r1.rename θ.ρ.cvar) (r2.rename θ.ρ.cvar) := by
  induction h
  case s_symm ih => apply s_symm; easy
  case s_ro =>
    apply s_ro <;> (apply RORoot.rebind; easy)
  case s_rw ih =>
    simp [CaptureRoot.rename] at *
    apply s_rw; easy
  case s_sep hb hrea =>
    rw [CaptureRoot.rename]
    apply s_sep
    have hb' := θ.cvar hb; easy
    apply ReachRoot.rebind hrea
  case s_fresh hc1 hc2 hneq =>
    simp [CaptureRoot.rename]
    apply s_fresh
    { have hc1' := θ.cvar hc1; easy }
    { have hc2' := θ.cvar hc2; easy }
    apply θ.fresh_inj hc1 hc2 hneq

theorem Separation.rebind
  (h : Separation Γ C1 C2)
  (θ : Rebinding Γ Δ) :
  Separation Δ (C1.rename θ.ρ.asCapt) (C2.rename θ.ρ.asCapt) := by
  apply ForallRoot.rebind
    (P := λ r1 => ForallRoot Γ C2 (λ r2 => RootSeparation Γ r1 r2))
    (Q := λ r1 => ForallRoot Δ (C2.rename θ.ρ.asCapt) (λ r2 => RootSeparation Δ r1 r2))
    (h := h)
    (θ := θ)
  intro r1 h'
  apply ForallRoot.rebind
    (P := λ r2 => RootSeparation Γ r1 r2)
    (Q := λ r2 => RootSeparation Δ (r1.rename θ.ρ.cvar) r2)
    (h := h')
    (θ := θ)
  intro r2 h''
  apply RootSeparation.rebind h''

end Capybara
