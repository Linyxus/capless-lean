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

end Capybara
