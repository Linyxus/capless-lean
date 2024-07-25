import Mathlib.Init.Function
import Aesop

namespace Capless

def FinFun (n n' : Nat) : Type :=
  Fin n -> Fin n'

def FinFun.id : FinFun n n :=
  fun i => i

def FinFun.weaken : FinFun n (n+1) :=
  Fin.succ

theorem FinFun.weaken_inj {n : Nat} : Function.Injective (weaken (n := n)) := by
  intro a b h
  unfold weaken at h
  simp [Fin.succ_inj] at h
  trivial

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

theorem FinFun.comp_weaken {f : FinFun n n'} :
  weaken ∘ f = f.ext ∘ weaken := by
  funext i
  cases n
  case zero => exact rfl
  case succ =>
    cases i using Fin.cases
    case zero => exact rfl
    case succ j => exact rfl

theorem FinFun.ext_comp_ext {f : FinFun n n'} {g : FinFun n' n''} :
  g.ext ∘ f.ext = FinFun.ext (g ∘ f) := by
  funext i
  cases i using Fin.cases
  case zero => exact rfl
  case succ j => exact rfl

theorem FinFun.open_comp {f : FinFun n n'} {x : Fin n} :
  f ∘ FinFun.open x = FinFun.open (f x) ∘ f.ext := by
  funext i
  cases i using Fin.cases
  case zero => exact rfl
  case succ j => exact rfl

theorem FinFun.open_comp_weaken :
  (FinFun.open x) ∘ weaken = id := by
  funext i
  simp [weaken, FinFun.open, id]

theorem FinFun.id_ext :
  (FinFun.ext (n := n) id) = id := by
  funext i
  cases i using Fin.cases
  case zero => simp [FinFun.ext, id]
  case succ i0 => simp [FinFun.ext, id]

lemma FinFun.comp_succ {f : FinFun n n'}: Fin.succ ∘ f = (FinFun.ext f) ∘ Fin.succ := by
  funext i
  cases n
  case zero =>
    aesop
  case succ n =>
    simp [FinFun.ext]

end Capless
