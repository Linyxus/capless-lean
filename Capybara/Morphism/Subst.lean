import Capybara.Syntax.Type
import Capybara.Syntax.CaptureSet
namespace Capybara

structure Subst (n m k n' m' k' : Nat) where
  var  : FinFun n n'
  tvar : Fin m -> SType n' m' k'
  cvar : Fin k -> CaptureSet n' k'

def Renaming.lift (ρ : Renaming n1 m1 k1 n2 m2 k2) : Subst n1 m1 k1 n2 m2 k2 := by
  constructor
  case var => exact ρ.var
  case tvar =>
    intro x
    apply SType.tvar
    exact ρ.tvar x
  case cvar =>
    intro c
    exact {c=ρ.cvar c}

end Capybara
