import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.PImage
import Capless.Basic
import Capless.Classifier
import Capless.Tactics
namespace Capless

/-!
# Capture Sets

This file contains the definition of capture sets.
-/

inductive Singleton : Nat -> Nat -> Type where
  | singl : Fin n -> Singleton n k
  | csingl : Fin k -> Singleton n k

/-- Projected captures -/
inductive Proj : Nat -> Nat -> Type where
  | proj : Singleton n k -> Kind -> Proj n k
  | capt : Singleton n k -> Proj n k

/-- Capture sets in System Capless.

The type of capture sets is parameterized by:
- `n` : the number of term variables in scope
- `k` : the number of capture variables in scope
This is due to the intrisincally-scoped method used in this mechanization.

Capture sets are defined inductively with four constructors:
- `empty` : the empty capture set
- `union` : the union of two capture sets
- `singleton` : a singleton set containing a term variable. The term variable is represented by a `Fin n`.
- `csingleton` : a singleton set containing a capture variable. The capture variable is represented by a `Fin k`.

Since the capture sets are indexed with the number of available binders, and each binder reference is represented by a `Fin`, capture sets are well-formed by construction.
-/
inductive CaptureSet : Nat -> Nat -> Type where
| empty : CaptureSet n k
| union : CaptureSet n k -> CaptureSet n k -> CaptureSet n k
| singleton : Proj n k -> CaptureSet n k

@[simp]
instance : EmptyCollection (CaptureSet n k) where
  emptyCollection := CaptureSet.empty

notation:max "{x=" x "}" => CaptureSet.singleton (Proj.capt (Singleton.singl x))
notation:max "{c=" c "}" => CaptureSet.singleton (Proj.capt (Singleton.csingl c))

@[simp]
instance : Union (CaptureSet n k) where
  union := CaptureSet.union

/-- Subset relation on capture sets. -/
inductive CaptureSet.Subset : CaptureSet n k → CaptureSet n k → Prop where
| empty : Subset {} C
| rfl : Subset C C
| union_l :
  Subset C1 C ->
  Subset C2 C ->
  Subset (C1 ∪ C2) C
| union_rl :
  Subset C C1 ->
  Subset C (C1 ∪ C2)
| union_rr :
  Subset C C2 ->
  Subset C (C1 ∪ C2)

@[simp]
instance : HasSubset (CaptureSet n k) where
  Subset := CaptureSet.Subset

-- @[simp]
-- def CaptureSet.proj (C: CaptureSet n k) (K: Kind) : CaptureSet n k :=
  -- match C with
  -- | empty => empty
  -- | union C1 C2 => union (C1.proj K) (C2.proj K)
  -- | singleton


/-!
## Renaming operations
-/

@[simp]
def Singleton.rename (s: Singleton n k) (f : FinFun n n') : Singleton n' k :=
  match s with
  | singl x => singl $ f x
  | csingl c => csingl c

@[simp]
def Proj.rename (s: Proj n k) (f : FinFun n n') : Proj n' k :=
  match s with
  | proj x k => proj (x.rename f) k
  | capt x => capt $ x.rename f

@[simp]
def CaptureSet.rename (C : CaptureSet n k) (f : FinFun n n') : CaptureSet n' k :=
  match C with
  | empty => empty
  | union C1 C2 => (C1.rename f) ∪ (C2.rename f)
  | singleton x => singleton $ x.rename f

@[simp]
def Singleton.crename (s: Singleton n k) (f : FinFun k k') : Singleton n k' :=
  match s with
  | singl x => singl x
  | csingl c => csingl $ f c

@[simp]
def Proj.crename (s: Proj n k) (f : FinFun k k') : Proj n k' :=
  match s with
  | proj x k => proj (x.crename f) k
  | capt x => capt $ x.crename f

@[simp]
def CaptureSet.crename (C : CaptureSet n k) (f : FinFun k k') : CaptureSet n k' :=
  match C with
  | empty => empty
  | union C1 C2 => (C1.crename f) ∪ (C2.crename f)
  | singleton x => singleton $ x.crename f

def CaptureSet.weaken (C : CaptureSet n k) : CaptureSet (n+1) k :=
  C.rename FinFun.weaken

def CaptureSet.weaken1 (C : CaptureSet (n+1) k) : CaptureSet (n+2) k :=
  C.rename FinFun.weaken.ext

def CaptureSet.cweaken (C : CaptureSet n k) : CaptureSet n (k+1) :=
  C.crename FinFun.weaken

def CaptureSet.cweaken1 (C : CaptureSet n (k+1)) : CaptureSet n (k+2) :=
  C.crename FinFun.weaken.ext

def CaptureSet.open (C : CaptureSet (n+1) k) (x : Fin n) : CaptureSet n k :=
  C.rename (FinFun.open x)

def CaptureSet.copen (C : CaptureSet n (k+1)) (x : Fin k) : CaptureSet n k :=
  C.crename (FinFun.open x)

/-!
## Basic Properties
-/

theorem CaptureSet.rename_union {C1 C2 : CaptureSet n k} {f : FinFun n n'} :
  (C1 ∪ C2).rename f = C1.rename f ∪ C2.rename f := by simp

theorem CaptureSet.crename_union {C1 C2 : CaptureSet n k} {f : FinFun k k'} :
  (C1 ∪ C2).crename f = C1.crename f ∪ C2.crename f := by simp

theorem CaptureSet.cweaken_union {C1 C2 : CaptureSet n k} :
  (C1 ∪ C2).cweaken = C1.cweaken ∪ C2.cweaken := by
  simp [CaptureSet.cweaken, CaptureSet.crename_union]

theorem CaptureSet.rename_singleton {x : Fin n} {f : FinFun n n'} :
  ({x=x} : CaptureSet n k).rename f = {x=f x} := by simp

theorem CaptureSet.ext_rename_singleton_zero {f : FinFun n n'} :
  ({x=0} : CaptureSet (n+1) k).rename f.ext = {x=0} := by
  simp [FinFun.ext]

theorem CaptureSet.rename_csingleton {x : Fin k} {f : FinFun n n'} :
  {c=x}.rename f = {c=x} := by simp

theorem CaptureSet.crename_singleton {x : Fin n} {f : FinFun k k'} :
  {x=x}.crename f = {x=x} := by simp

theorem CaptureSet.crename_csingleton {x : Fin k} {f : FinFun k k'} :
  ({c=x} : CaptureSet n k).crename f = {c=f x} := by simp

theorem CaptureSet.rename_empty :
  ({} : CaptureSet n k).rename f = {} := by simp

theorem CaptureSet.crename_empty :
  ({} : CaptureSet n k).crename f = {} := by simp

theorem CaptureSet.crename_rename_comm {C : CaptureSet n k} {f : FinFun n n'} {g : FinFun k k'} :
  (C.rename f).crename g = (C.crename g).rename f := by
  induction C <;> aesop

theorem CaptureSet.copen_rename_comm {C : CaptureSet n (k+1)} {x : Fin k} {f : FinFun n n'} :
  (C.copen x).rename f = (C.rename f).copen x := by
  simp [copen, crename_rename_comm]

theorem CaptureSet.cweaken_rename_comm {C : CaptureSet n k} {f : FinFun n n'} :
  (C.cweaken).rename f = (C.rename f).cweaken := by
  simp [cweaken, crename_rename_comm]

theorem CaptureSet.rename_rename {C : CaptureSet n k} :
  (C.rename f).rename g = C.rename (g ∘ f) := by
  induction C <;> aesop

theorem CaptureSet.weaken_rename {C : CaptureSet n k} :
  (C.rename f).weaken = C.weaken.rename f.ext := by
  simp [weaken, rename_rename, FinFun.comp_weaken]

theorem CaptureSet.weaken_crename {C : CaptureSet n k} :
  (C.crename f).weaken = C.weaken.crename f := by
  simp [weaken, crename_rename_comm]

theorem CaptureSet.crename_crename {C : CaptureSet n k} :
  (C.crename f).crename g = C.crename (g ∘ f) := by
  induction C <;> aesop

theorem CaptureSet.crename_copen {C : CaptureSet n (k+1)} :
  (C.copen c).crename f = (C.crename f.ext).copen (f c) :=
  by simp [copen, crename_crename, FinFun.open_comp]

theorem CaptureSet.cweaken_crename {C : CaptureSet n k} :
  (C.crename f).cweaken = C.cweaken.crename f.ext := by
  simp [cweaken, crename_crename, FinFun.comp_weaken]

theorem CaptureSet.subset_refl {C : CaptureSet n k} :
  C ⊆ C := by constructor

theorem CaptureSet.cweaken_csingleton {c : Fin k} :
  ({c=c} : CaptureSet n k).cweaken = {c=c.succ} := by
  simp [singleton, cweaken, crename, FinFun.weaken]

theorem CaptureSet.weaken_csingleton :
  ({c=c} : CaptureSet n k).weaken = {c=c} := by
  simp [singleton, weaken]

theorem CaptureSet.rename_id {C : CaptureSet n k} :
  C.rename FinFun.id = C := by
  induction C <;> aesop

theorem CaptureSet.crename_id {C : CaptureSet n k} :
  C.crename FinFun.id = C := by
  induction C <;> aesop

theorem CaptureSet.crename_monotone {C1 C2 : CaptureSet n k} {f : FinFun k k'}
  (h : C1 ⊆ C2) :
  C1.crename f ⊆ C2.crename f := by
  induction h <;> try (solve | constructor | simp; constructor <;> trivial)
  case union_rr =>
    simp
    apply! Subset.union_rr

theorem CaptureSet.cweaken_monotone {C1 C2 : CaptureSet n k}
  (h : C1 ⊆ C2) :
  C1.cweaken ⊆ C2.cweaken := by
  induction h <;> try (solve | constructor | simp; constructor <;> trivial)
  case union_rr =>
    simp
    apply! Subset.union_rr

theorem CaptureSet.cweaken_def {C : CaptureSet n k} :
  C.cweaken = C.crename FinFun.weaken := by
  induction C <;> aesop

end Capless
