import Capybara.Morphism.Rebinding
import Capybara.StaticSemantics
namespace Capybara

/-!
This file proves that rebinding preserves judgements over capture roots.
-/

/-!
Rebinding preserves root reachability (deprecated)
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

/-!
Rebinding preserves the "forall roots" judgement.
-/
theorem ForallRoot.rebind {n m k n' m' k'}
  {Γ : Context n m k} {Δ : Context n' m' k'} {C : CaptureSet n k}
  (P : RootPred k) (Q : RootPred k')
  (h : ForallRoot Γ C P)
  (θ : Rebinding Γ Δ)
  (transport : ∀r, P r -> Q (r.rename θ.ρ.cvar)) :
  ForallRoot Δ (C.rename θ.ρ.asCapt) Q := by
  induction h
  case r_union ih1 ih2 =>
    rw [CaptureSet.rename_union]
    apply r_union <;> aesop
  case r_var hb _ ih =>
    simp [CaptureSet.rename]
    apply r_var
    { have hb' := θ.var hb; easy }
    { repeat rw [<-CaptureSet.qualified_rename]
      apply ih; easy }
  case r_cvar_alias hb _ ih =>
    simp [CaptureSet.rename]
    apply r_cvar_alias
    { have hb' := θ.cvar hb; easy }
    { repeat rw [<-CaptureSet.qualified_rename]
      apply ih; easy }
  case r_cvar hc hp =>
    apply r_cvar
    have hc' := θ.cvar hc; easy
    have hp' := transport _ hp; easy

/-!
The following three theorems show that rebinding preserves the kinding of capture roots.
-/
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
theorem MutRoot.rebind
  (h : MutRoot Γ r)
  (θ : Rebinding Γ Δ) :
  MutRoot Δ (r.rename θ.ρ.cvar) := by
  cases h
  case r_mut =>
    apply r_mut
theorem FreshRoot.rebind
  (h : FreshRoot Γ r)
  (θ : Rebinding Γ Δ) :
  FreshRoot Δ (r.rename θ.ρ.cvar) := by
  cases h
  case r_fresh hc =>
    apply r_fresh
    have hc' := θ.cvar hc; easy

end Capybara
