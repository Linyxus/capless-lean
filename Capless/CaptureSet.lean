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

instance CaptureSet.empty : EmptyCollection (CaptureSet n k) where
  emptyCollection := ⟨∅, ∅, ∅⟩

instance CaptureSet.union : Union (CaptureSet n k) where
  union c1 c2 :=
    ⟨c1.vars ∪ c2.vars, c1.rvars ∪ c2.rvars, c1.cvars ∪ c2.cvars⟩

instance : HasSubset (CaptureSet n k) where
  Subset := CaptureSet.Subset

instance CaptureSet.singleton : Singleton (Fin n) (CaptureSet n k) where
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

theorem CaptureSet.rename_union {C1 C2 : CaptureSet n k} {f : FinFun n n'} :
  (C1 ∪ C2).rename f = C1.rename f ∪ C2.rename f := by
  cases C1; cases C2; simp [CaptureSet.rename, CaptureSet.union]
  simp [Finset.image_union]

theorem CaptureSet.crename_union {C1 C2 : CaptureSet n k} {f : FinFun k k'} :
  (C1 ∪ C2).crename f = C1.crename f ∪ C2.crename f := by
  cases C1; cases C2; simp [CaptureSet.crename, CaptureSet.union]
  simp [Finset.image_union]

theorem CaptureSet.rename_singleton {x : Fin n} {f : FinFun n n'} :
  ({x} : CaptureSet n k).rename f = {f x} := by
  simp [CaptureSet.rename, Finset.image_singleton, CaptureSet.singleton]

theorem CaptureSet.rename_csingleton {x : Fin k} {f : FinFun n n'} :
  (CaptureSet.csingleton x).rename f = CaptureSet.csingleton x := by
  simp [CaptureSet.rename, CaptureSet.csingleton]

theorem CaptureSet.crename_rename_comm {C : CaptureSet n k} {f : FinFun n n'} {g : FinFun k k'} :
  (C.rename f).crename g = (C.crename g).rename f := by
  cases C; simp [CaptureSet.rename, CaptureSet.crename, Finset.image_image]

theorem CaptureSet.copen_rename_comm {C : CaptureSet n (k+1)} {x : Fin k} {f : FinFun n n'} :
  (C.copen x).rename f = (C.rename f).copen x := by
  simp [copen, crename_rename_comm]

theorem CaptureSet.cweaken_rename_comm {C : CaptureSet n k} {f : FinFun n n'} :
  (C.cweaken).rename f = (C.rename f).cweaken := by
  simp [cweaken, crename_rename_comm]

theorem CaptureSet.rename_rename {C : CaptureSet n k} :
  (C.rename f).rename g = C.rename (g ∘ f) := by
  cases C; simp [CaptureSet.rename, Finset.image_image]

theorem CaptureSet.weaken_rename {C : CaptureSet n k} :
  (C.rename f).weaken = C.weaken.rename f.ext := by
  simp [weaken, rename_rename, FinFun.comp_weaken]

end Capless
