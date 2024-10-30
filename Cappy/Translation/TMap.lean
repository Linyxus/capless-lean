import Aesop
import Mathlib.Data.Fin.Basic
import Capless.Basic
namespace Cappy

structure TMap (n m k : Nat) where
  reach : Fin n -> Fin k
  treach : Fin m -> Fin k

def TMap.empty : TMap 0 0 0 := ⟨id, id⟩

def TMap.ext (ρ : TMap n m k) : TMap (n+1) m (k+1) := by
  constructor
  case reach =>
    have h := ρ.reach
    apply Capless.FinFun.ext
    aesop
  case treach =>
    have h := ρ.treach
    intro x
    apply Fin.succ
    aesop

def TMap.text (ρ : TMap n m k) : TMap n (m+1) (k+1) := by
  constructor
  case reach =>
    have h := ρ.reach
    intro x
    apply Fin.succ
    aesop
  case treach =>
    have h := ρ.treach
    apply Capless.FinFun.ext
    aesop

def TMap.cweaken (ρ : TMap n m k) : TMap n m (k+1) := by
  constructor
  case reach =>
    have h := ρ.reach
    intro x
    apply Fin.succ
    aesop
  case treach =>
    have h := ρ.treach
    intro x
    apply Fin.succ
    aesop

def TMap.strip (ρ : TMap (n+1) m k) : TMap n m k := by
  constructor
  case reach =>
    have h := ρ.reach
    intro n
    exact h (n.succ)
  case treach =>
    have h := ρ.treach
    aesop

def TMap.tstrip (ρ : TMap n (m+1) k) : TMap n m k := by
  constructor
  case reach =>
    have h := ρ.reach
    aesop
  case treach =>
    have h := ρ.treach
    intro m
    exact h (m.succ)

end Cappy
