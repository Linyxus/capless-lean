import Capybara.Syntax.Type.Renaming
namespace Capybara

def CType.copen (T : CType n m (k+1)) (c : Fin k) : CType n m k :=
  T.rename (Renaming.copen c)

def EType.open (T : EType (n+1) m k) (x : Fin n) : EType n m k :=
  T.rename (Renaming.open x)

def EType.topen (T : EType n (m+1) k) (X : Fin m) : EType n m k :=
  T.rename (Renaming.topen X)

def EType.copen (T : EType n m (k+1)) (c : Fin k) : EType n m k :=
  T.rename (Renaming.copen c)

end Capybara
