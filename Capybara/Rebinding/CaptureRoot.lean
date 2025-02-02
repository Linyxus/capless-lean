import Capybara.Morphism.Rebinding
import Capybara.StaticSemantics
namespace Capybara

/-!
This file proves that rebinding preserves capture root reachability.
-/

theorem ReachRoot.rebind
  (h : ReachRoot Γ C r)
  (θ : Rebinding Γ Δ) :
  ReachRoot Δ (C.rename θ.ρ.asCapt) (r.rename θ.ρ.cvar) := by
  induction h
  case union_l ih =>
    rw [CaptureSet.rename_union]
    simp [CaptureRoot.rename] at *
    apply union_l
    easy
  case union_r ih =>
    rw [CaptureSet.rename_union]
    simp [CaptureRoot.rename] at *
    apply union_r
    easy
  case var hb _ ih =>
    simp [CaptureSet.rename]
    simp [CaptureRoot.rename] at *
    apply var
    { have hb' := θ.var hb; easy }
    { repeat rw [<-CaptureSet.qualified_rename]
      easy }
  case cvar_alias hb _ ih =>
    simp [CaptureSet.rename]
    simp [CaptureRoot.rename] at *
    apply cvar_alias
    { have hb' := θ.cvar hb; easy }
    { repeat rw [<-CaptureSet.qualified_rename]
      easy }
  case cvar hb =>
    simp [CaptureSet.rename]
    apply cvar
    have hb' := θ.cvar hb; easy

theorem RORoot.rebind
  (h : RORoot Γ r)
  (θ : Rebinding Γ Δ) :
  RORoot Δ (r.rename θ.ρ.cvar) := by
  cases h
  case r_ro =>
    apply r_ro
  case r_imm hc =>
    apply r_imm
    have hc' := θ.cvar hc; easy

theorem ReachRoot.rebind_inv'
  (θ : Rebinding Γ Δ)
  (he : C0 = C.rename θ.ρ.asCapt)
  (h : ReachRoot Δ C0 r) :
  ∃ r0, ReachRoot Γ C r0 ∧ r0.rename θ.ρ.cvar = r := by
  induction h generalizing C
  case union_l ih =>
    cases C <;> simp [CaptureSet.rename] at he
    case union D1 D2 =>
      have ⟨he, _⟩ := he
      have ⟨r0, h0, h1⟩ := ih he
      apply Exists.intro r0
      constructor
      { apply union_l; easy }
      { easy }
  case union_r ih =>
    cases C <;> simp [CaptureSet.rename] at he
    case union D1 D2 =>
      have ⟨_, he⟩ := he
      have ⟨r0, h0, h1⟩ := ih he
      apply Exists.intro r0
      constructor
      { apply union_r; easy }
      { easy }
  case var => sorry
  case cvar_alias => sorry
  case cvar => sorry

theorem ReachRoot.rebind_inv
  (θ : Rebinding Γ Δ)
  (h : ReachRoot Δ (C.rename θ.ρ.asCapt) r) :
  ∃ r0, ReachRoot Γ C r0 ∧ r0.rename θ.ρ.cvar = r := sorry


end Capybara
