import Capybara.Syntax.Type.Renaming
namespace Capybara

def CType.copen (T : CType n m (k+1)) (c : Fin k) : CType n m k :=
  T.rename (Renaming.copen c)

end Capybara
