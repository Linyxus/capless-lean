import Capless.Tactics
import Capybara.Syntax
import Capybara.Morphism.Core
namespace Capybara

/-!
# Rebinding

A rebinding is a morphism from a source context `Γ` to a target context `Δ` that maps each binding in `Γ` to an equivalent one in `Δ`.
-/
structure Rebinding (Γ : Context n m k) (Δ : Context n' m' k') where
  ρ : Renaming n m k n' m' k'
  var : ∀ {x T}, Γ.Lookup x T -> Δ.Lookup (ρ.var x) (T.rename ρ)
  tvar : ∀ {X S}, Γ.LookupT X S -> Δ.LookupT (ρ.tvar X) (S.rename ρ)
  cvar : ∀ {c K}, Γ.LookupC c K -> Δ.LookupC (ρ.cvar c) (K.rename ρ.asCapt)

def Rebinding.ext (θ : Rebinding Γ Δ) : Rebinding (Γ,x:T) (Δ,x:T.rename θ.ρ) := by
  constructor
  case ρ => exact θ.ρ.ext
  case var =>
    intro x T hb
    cases hb with
    | here =>
      simp [Renaming.ext_var_zero]
      simp [<-CType.rename_weaken]
      constructor
    | there h =>
      simp [Renaming.ext_var_succ]
      simp [<-CType.rename_weaken]
      constructor
      apply θ.var; easy
  case tvar =>
    intro X S hb
    cases hb
    case there hb =>
      simp [<-TBinding.rename_weaken]
      constructor
      apply θ.tvar; easy
  case cvar =>
    intro c B hb
    cases hb
    case there hb =>
      simp [<-CBinding.rename_weaken]
      constructor
      apply θ.cvar; easy

def Rebinding.text (θ : Rebinding Γ Δ) : Rebinding (Γ,X:B) (Δ,X:B.rename θ.ρ) := by
  constructor
  case ρ => exact θ.ρ.text
  case var =>
    intro x T hb
    cases hb
    case tthere hb =>
      simp [<-CType.rename_tweaken]
      constructor
      apply θ.var; easy
  case tvar =>
    intro X B hb
    cases hb
    case here =>
      simp [<-TBinding.rename_tweaken]
      constructor
    case tthere hb =>
      simp [<-TBinding.rename_tweaken]
      constructor
      apply θ.tvar; easy
  case cvar =>
    intro c B hb
    cases hb
    case tthere hb =>
      simp
      constructor
      apply θ.cvar; easy

end Capybara
