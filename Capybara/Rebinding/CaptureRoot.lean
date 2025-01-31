import Capybara.Morphism.Rebinding
import Capybara.StaticSemantics
namespace Capybara

def CaptureRoot.rename (r : CaptureRoot k) (f : FinFun k k') : CaptureRoot k' :=
  match r with
  | ⟨m,c⟩ => ⟨m,f c⟩

theorem ReachRoot.rename
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
    simp [CaptureSet.rename, ReachRoot.rename]
    apply cvar
    have hb' := θ.cvar hb; easy

end Capybara
