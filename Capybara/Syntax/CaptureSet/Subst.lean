import Capybara.Syntax.CaptureSet.Core
import Capybara.Morphism.Subst
namespace Capybara

def CaptureSet.subst
  (C : CaptureSet n k)
  (σ : Subst n m k n' m' k') :
  CaptureSet n' k' :=
  match C with
  | empty => {}
  | union C1 C2 => (C1.subst σ) ∪ (C2.subst σ)
  | singleton x m => {x@m:=σ.var x}
  | csingleton c m => (σ.cvar c).qualified m

end Capybara
