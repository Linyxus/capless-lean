import Mathlib.Data.Fin.Basic
namespace Capybara

def FinFun (n : Nat) (n' : Nat) : Type := Fin n -> Fin n'

def FinFun.ext (f : FinFun n n') : FinFun (n+1) (n'+1) := by
  intro x
  cases x using Fin.cases
  case zero => exact 0
  case succ x0 => exact Fin.succ (f x0)

structure Renaming (n m k n' m' k' : Nat) where
  var : FinFun n n'
  tvar : FinFun m m'
  cvar : FinFun k k'

def Renaming.ext (ρ : Renaming n m k n' m' k') :
  Renaming (n+1) m k (n'+1) m' k' :=
  {
    var := ρ.var.ext
    tvar := ρ.tvar
    cvar := ρ.cvar
  }

def Renaming.text (ρ : Renaming n m k n' m' k') :
  Renaming n (m+1) k n' (m'+1) k' :=
  {
    var := ρ.var
    tvar := ρ.tvar.ext
    cvar := ρ.cvar
  }

def Renaming.cext (ρ : Renaming n m k n' m' k') :
  Renaming n m (k+1) n' m' (k'+1) :=
  {
    var := ρ.var
    tvar := ρ.tvar
    cvar := ρ.cvar.ext
  }

end Capybara
