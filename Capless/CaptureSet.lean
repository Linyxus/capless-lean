import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.PImage
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

def CaptureSet.rsingleton (x : Fin n) : CaptureSet n k :=
  ⟨∅, {x}, ∅⟩

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

theorem CaptureSet.rename_rsingleton {x : Fin n} {f : FinFun n n'} :
  (CaptureSet.rsingleton x : CaptureSet n k).rename f = CaptureSet.rsingleton (f x) := by
  simp [CaptureSet.rename, CaptureSet.rsingleton]

theorem CaptureSet.crename_singleton {x : Fin n} {f : FinFun k k'} :
  ({x} : CaptureSet n k).crename f = {x} := by
  simp [CaptureSet.crename, CaptureSet.singleton]

theorem CaptureSet.crename_csingleton {x : Fin k} {f : FinFun k k'} :
  (CaptureSet.csingleton x : CaptureSet n k).crename f = CaptureSet.csingleton (f x) := by
  simp [CaptureSet.crename, CaptureSet.csingleton]

theorem CaptureSet.crename_rsingleton {x : Fin n} {f : FinFun k k'} :
  (CaptureSet.rsingleton x : CaptureSet n k).crename f = CaptureSet.rsingleton x := by
  simp [CaptureSet.crename, CaptureSet.rsingleton]

theorem CaptureSet.rename_empty :
  ({} : CaptureSet n k).rename f = {} := by
  simp [CaptureSet.rename, CaptureSet.empty, Finset.image_empty]

theorem CaptureSet.crename_empty :
  ({} : CaptureSet n k).crename f = {} := by
  simp [CaptureSet.crename, CaptureSet.empty, Finset.image_empty]

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

theorem CaptureSet.weaken_crename {C : CaptureSet n k} :
  (C.crename f).weaken = C.weaken.crename f := by
  simp [weaken, crename_rename_comm]

theorem CaptureSet.crename_crename {C : CaptureSet n k} :
  (C.crename f).crename g = C.crename (g ∘ f) := by
  cases C; simp [CaptureSet.crename, Finset.image_image]

theorem CaptureSet.crename_copen {C : CaptureSet n (k+1)} :
  (C.copen c).crename f = (C.crename f.ext).copen (f c) :=
  by simp [copen, crename_crename, FinFun.open_comp]

inductive CaptureSet.NonLocal : CaptureSet (n+1) k -> Prop where
| mk : ∀ {C : CaptureSet (n+1) k},
  0 ∉ C.vars ->
  0 ∉ C.rvars ->
  C.NonLocal

theorem Finset.nonlocal_rename_l
  (he : xs0 = Finset.image (FinFun.ext f) xs)
  (h : 0 ∉ xs0) :
  0 ∉ xs := by
  intro h0
  apply h
  subst he
  have heq : FinFun.ext f 0 = 0 := by rfl
  rw [<- heq]
  apply Finset.mem_image_of_mem
  trivial

theorem CaptureSet.nonlocal_rename_l
  (he : C0 = C.rename (FinFun.ext f))
  (h : NonLocal C0) :
  NonLocal C := by
  cases C0; cases C
  cases h
  case mk h1 h2 =>
    simp [CaptureSet.rename] at he
    simp at *
    let ⟨he1, he2, he3⟩ := he
    subst he1 he2
    constructor <;> simp
    apply Finset.nonlocal_rename_l rfl h1
    apply Finset.nonlocal_rename_l rfl h2

theorem CaptureSet.nonlocal_crename_l
  (he : C0 = C.crename f)
  (h : NonLocal C0) :
  NonLocal C := by
  cases C0; cases C
  cases h
  case mk h1 h2 =>
    simp [CaptureSet.crename] at he
    simp at *
    let ⟨he1, he2, he3⟩ := he
    subst he1 he2
    constructor <;> simp
    assumption
    assumption



theorem Finset.nonlocal_rename_r
  (h : 0 ∉ xs) :
  0 ∉ Finset.image (FinFun.ext f) xs := by
  intro h0
  apply h
  rw [Finset.mem_image] at h0
  let ⟨a0, he, heq⟩ := h0
  cases a0 using Fin.cases
  case zero => trivial
  case succ a1 =>
    simp [FinFun.ext] at heq
    cases heq

theorem CaptureSet.nonlocal_rename_r
  (h : NonLocal C) :
  NonLocal (C.rename (FinFun.ext f)) := by
  cases C; cases h
  case mk h1 h2 =>
    simp at *
    constructor <;> simp only [CaptureSet.rename]
    apply Finset.nonlocal_rename_r h1
    apply Finset.nonlocal_rename_r h2

theorem CaptureSet.nonlocal_crename_r
  (h : NonLocal C) :
  NonLocal (C.crename f) := by
  cases C; cases h
  case mk h1 h2 =>
    simp at *
    constructor <;> simp only [CaptureSet.crename]
    assumption
    assumption

theorem CaptureSet.cweaken_crename {C : CaptureSet n k} :
  (C.crename f).cweaken = C.cweaken.crename f.ext := by
  simp [cweaken, crename_crename, FinFun.comp_weaken]

theorem CaptureSet.subset_refl {C : CaptureSet n k} :
  C ⊆ C := by
  cases C
  constructor <;> (rw [Finset.subset_iff]; intros; trivial)

def Fin.ppred : Fin (n+1) →. Fin n := by
  intro i
  constructor
  case Dom => exact (i ≠ 0)
  case get =>
    intro h
    exact i.pred h

instance : ∀ (x : Fin (n+1)), Decidable (Fin.ppred x).Dom := by
  intro x
  simp [Fin.ppred]
  apply instDecidableNot

def Finset.pred (xs : Finset (Fin (n+1))) : Finset (Fin n) :=
  xs.pimage Fin.ppred


theorem Finset.notin_weaken {xs : Finset (Fin (n+1))} :
  0 ∉ xs -> (Finset.pred xs).image Fin.succ = xs := by
  intro h
  rw [Finset.ext_iff]
  intro a
  constructor
  case mp =>
    intro he
    sorry
  case mpr => sorry

end Capless
