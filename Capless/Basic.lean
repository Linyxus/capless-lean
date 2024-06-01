namespace Capless

def FinFun (n n' : Nat) : Type :=
  Fin n -> Fin n'

def FinFun.id : FinFun n n :=
  fun i => i

def FinFun.weaken : FinFun n (n+1) :=
  Fin.succ

def FinFun.open (x : Fin n) : FinFun (n+1) n := by
  intro i
  cases i using Fin.cases
  case zero => exact x
  case succ j => exact j

def FinFun.ext (f : FinFun n n') : FinFun (n+1) (n'+1) := by
  intro i
  cases i using Fin.cases
  case zero => exact 0
  case succ j => exact Fin.succ (f j)

end Capless
