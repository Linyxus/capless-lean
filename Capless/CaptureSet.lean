import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Capless.Basic
namespace Capless

/-!

# Capture Sets

!-/

structure CaptureSet (n k : Nat) where
  vars : Finset (Fin n)
  rvars : Finset (Fin n)
  cvars : Finset (Fin k)

inductive CaptureSet.Subset : CaptureSet n k → CaptureSet n k → Prop where
  | mk : ∀ {c1 c2 : CaptureSet n k},
    c1.vars ⊆ c2.vars →
    c1.rvars ⊆ c2.rvars →
    c1.cvars ⊆ c2.cvars →
    Subset c1 c2

instance : EmptyCollection (CaptureSet n k) where
  emptyCollection := ⟨∅, ∅, ∅⟩

instance : Union (CaptureSet n k) where
  union c1 c2 :=
    ⟨c1.vars ∪ c2.vars, c1.rvars ∪ c2.rvars, c1.cvars ∪ c2.cvars⟩

instance : HasSubset (CaptureSet n k) where
  Subset := CaptureSet.Subset

instance : Singleton (Fin n) (CaptureSet n k) where
  singleton x := ⟨{x}, ∅, ∅⟩

-- instance : Singleton (Fin k) (CaptureSet n k) where
--   singleton x := ⟨∅, ∅, {x}⟩

def CaptureSet.csingleton (x : Fin k) : CaptureSet n k :=
  ⟨∅, ∅, {x}⟩

def CaptureSet.rename (C : CaptureSet n k) (f : FinFun n n') : CaptureSet n' k :=
  ⟨Finset.image f C.vars, Finset.image f C.rvars, C.cvars⟩

def CaptureSet.crename (C : CaptureSet n k) (f : FinFun k k') : CaptureSet n k' :=
  ⟨C.vars, C.rvars, Finset.image f C.cvars⟩

def CaptureSet.weaken (C : CaptureSet n k) : CaptureSet (n+1) k :=
  C.rename FinFun.weaken

def CaptureSet.cweaken (C : CaptureSet n k) : CaptureSet n (k+1) :=
  C.crename FinFun.weaken

def CaptureSet.open (C : CaptureSet (n+1) k) (x : Fin n) : CaptureSet n k :=
  C.rename (FinFun.open x)

def CaptureSet.copen (C : CaptureSet n (k+1)) (x : Fin k) : CaptureSet n k :=
  C.crename (FinFun.open x)

end Capless
