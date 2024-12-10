import Capybara.Morphism.Subst
import Capybara.Syntax.Type.Core
namespace Capybara

mutual

def EType.subst
  (E : EType n m k)
  (σ : Subst n m k n' m' k') :
  EType n' m' k' := sorry

def CType.subst
  (T : CType n m k)
  (σ : Subst n m k n' m' k') :
  CType n' m' k' := sorry

def SType.subst
  (S : SType n m k)
  (σ : Subst n m k n' m' k') :
  SType n' m' k' := sorry

end

end Capybara
