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
| var : Fin n -> Singleton n k
| cvar : Fin k -> Singleton n k

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
| singleton : Singleton n k -> Kind -> CaptureSet n k

@[simp]
def CaptureSet.proj (c : CaptureSet n k) (K : Kind) :=
  match c with
  | empty => empty
  | union c1 c2 => union (c1.proj K) (c2.proj K)
  | singleton s p => singleton s (p.intersect K)

theorem CaptureSet.proj_top {C : CaptureSet n k} : C.proj .top = C := by
  induction C
  case empty => aesop
  case union ha hb => aesop
  case singleton => simp; apply Kind.Intersect.top_r

@[simp]
instance : EmptyCollection (CaptureSet n k) where
  emptyCollection := CaptureSet.empty

notation:max "{x=" x " | " K "}" => CaptureSet.singleton (Singleton.var x) K
notation:max "{c=" c " | " K "}" => CaptureSet.singleton (Singleton.cvar c) K

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
| singleton_subkind :
  K.Subkind L ->
  Subset (.singleton s K) (.singleton s L)
| singleton_absurd :
  K.IsEmpty ->
  Subset (.singleton s K) .empty
| proj_merge:
  Subset (.singleton s (.union L1 L2)) (.union (.singleton s L1) (.singleton s L2))
| trans : Subset A B -> Subset B C -> Subset A C

@[simp]
instance : HasSubset (CaptureSet n k) where
  Subset := CaptureSet.Subset

theorem CaptureSet.Subset.union_l_inv (hs : Subset (.union a1 a2) b) : Subset a1 b ∧ Subset a2 b := by
  generalize h : (CaptureSet.union a1 a2) = C at hs
  induction hs generalizing a1 a2 <;> cases h
  case rfl =>
    apply And.intro
    apply union_rl .rfl
    apply union_rr .rfl
  case union_l => apply! And.intro
  case union_rl ha =>
    have ⟨_, _⟩ := ha (.refl _)
    apply And.intro <;> apply! union_rl
  case union_rr ha =>
    have ⟨_, _⟩ := ha (.refl _)
    apply And.intro <;> apply! union_rr
  case trans ha iha hb ihb =>
    have ⟨_, _⟩ := ihb (.refl _)
    apply And.intro <;> apply! trans _ ha


-- theorem CaptureSet.Subset.trans (hs1 : Subset a b) (hs2 : Subset b c) : Subset a c := by
--   induction hs1
--   case empty => constructor
--   case rfl => assumption
--   case union_l ha hb iha ihb =>
--     apply! union_l (iha _) (ihb _)
--   case union_rl ha iha =>
--     have ⟨_, _⟩ := hs2.union_l_inv
--     apply! iha
--   case union_rr ha iha =>
--     have ⟨_, _⟩ := hs2.union_l_inv
--     apply! iha
--   case singleton_subkind s K L hs =>
--     generalize h : (singleton s L) = D at hs2
--     induction hs2 <;> cases h
--     case rfl => apply! singleton_subkind
--     case union_rl ih => apply union_rl (ih (.refl _))
--     case union_rr ih => apply union_rr (ih (.refl _))
--     case singleton_subkind hs2 => apply singleton_subkind (hs.trans hs2)
--     case proj_merge hs2 => apply proj_merge (hs.trans hs2)
--   case proj_merge



@[simp]
instance : IsTrans (CaptureSet n k) (HasSubset.Subset) where
  trans a b c := CaptureSet.Subset.trans

theorem CaptureSet.Subset.union_monotone {C1 C2 D1 D2 : CaptureSet n k} (hc : Subset C1 C2) (hd : Subset D1 D2) : Subset (C1 ∪ D1) (C2 ∪ D2) := by
  apply union_l
  apply! union_rl
  apply! union_rr

theorem CaptureSet.Subset.subkind {C : CaptureSet n k}
  (hk : K.Subkind L)
  : Subset (C.proj K) (C.proj L) := by
  induction C
  case empty => simp; constructor
  case union ha hb => apply! union_monotone
  case singleton => simp; apply singleton_subkind (Kind.Intersect.with_subkind hk)

theorem CaptureSet.Subset.absurd {C : CaptureSet n k} (he : K.IsEmpty) : Subset (C.proj K) .empty := by
  induction C
  case empty => simp; constructor
  case union ha hb =>
    apply trans (.union_monotone ha hb)
    apply union_l .rfl .rfl
  case singleton => simp; apply singleton_absurd; apply Kind.Intersect.is_empty_r he

/-!
## Renaming operations
-/

@[simp]
def Singleton.rename (s : Singleton n k) (f : FinFun n n') : Singleton n' k :=
  match s with
  | var n => var $ f n
  | cvar k => cvar k

@[simp]
def Singleton.crename (s : Singleton n k) (f : FinFun k k') : Singleton n k' :=
  match s with
  | var n => var n
  | cvar k => cvar $ f k

@[simp]
theorem Singleton.rename_id {s : Singleton n k} :
  s.rename FinFun.id = s := by
  induction s <;> simp_all [FinFun.id]

@[simp]
theorem Singleton.crename_id {s : Singleton n k} :
  s.crename FinFun.id = s := by
  induction s <;> simp_all [FinFun.id]

@[simp]
theorem Singleton.rename_rename {s : Singleton n k} :
  (s.rename f).rename g = s.rename (g ∘ f) := by
  induction s <;> simp_all

@[simp]
theorem Singleton.crename_crename {s : Singleton n k} :
  (s.crename f).crename g = s.crename (g ∘ f) := by
  induction s <;> simp_all

@[simp]
theorem Singleton.crename_rename_comm {s : Singleton n k} {f : FinFun n n'} {g : FinFun k k'} :
  (s.rename f).crename g = (s.crename g).rename f := by
  induction s <;> simp_all

@[simp]
def CaptureSet.rename (C : CaptureSet n k) (f : FinFun n n') : CaptureSet n' k :=
  match C with
  | empty => empty
  | union C1 C2 => (C1.rename f) ∪ (C2.rename f)
  | singleton s p => singleton (s.rename f) p

@[simp]
def CaptureSet.crename (C : CaptureSet n k) (f : FinFun k k') : CaptureSet n k' :=
  match C with
  | empty => empty
  | union C1 C2 => (C1.crename f) ∪ (C2.crename f)
  | singleton s p => singleton (s.crename f) p

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
  ({x=x | K} : CaptureSet n k).rename f = {x=f x | K} := by simp

theorem CaptureSet.ext_rename_singleton_zero {f : FinFun n n'} :
  ({x=0 | K} : CaptureSet (n+1) k).rename f.ext = {x=0 | K} := by
  simp [FinFun.ext]

theorem CaptureSet.rename_csingleton {x : Fin k} {f : FinFun n n'} :
  {c=x | K}.rename f = {c=x | K} := by simp

theorem CaptureSet.crename_singleton {x : Fin n} {f : FinFun k k'} :
  {x=x | K}.crename f = {x=x | K} := by simp

theorem CaptureSet.crename_csingleton {x : Fin k} {f : FinFun k k'} :
  ({c=x | K} : CaptureSet n k).crename f = {c=f x | K} := by simp

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

theorem CaptureSet.cweaken_csingleton {c : Fin k} :
  ({c=c | K} : CaptureSet n k).cweaken = {c=c.succ | K} := by
  simp [singleton, cweaken, crename, FinFun.weaken]

theorem CaptureSet.weaken_csingleton :
  ({c=c | K} : CaptureSet n k).weaken = {c=c | K} := by
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
  induction h <;> simp
  case empty => constructor
  case rfl => constructor
  case union_l ha hb iha ihb =>
    apply! Subset.union_l
  case union_rl ha ih =>
    apply! Subset.union_rl
  case union_rr ha ih =>
    apply! Subset.union_rr
  case singleton_subkind s K L hk =>
    cases s <;> (simp; apply! Subset.singleton_subkind)
  case singleton_absurd s K he =>
    cases s <;> (simp; apply! Subset.singleton_absurd)
  case proj_merge s L1 L2 =>
    cases s <;> (simp; apply! Subset.proj_merge)
  case trans ha hb => apply! Subset.trans

theorem CaptureSet.cweaken_monotone {C1 C2 : CaptureSet n k}
  (h : C1 ⊆ C2) :
  C1.cweaken ⊆ C2.cweaken := by
  induction h <;> simp
  case empty => constructor
  case rfl => constructor
  case union_l ha hb iha ihb =>
    apply! Subset.union_l
  case union_rl ha ih =>
    apply! Subset.union_rl
  case union_rr ha ih =>
    apply! Subset.union_rr
  case singleton_subkind s K L hk =>
    cases s <;> (apply! Subset.singleton_subkind)
  case singleton_absurd s K he =>
    cases s <;> (apply! Subset.singleton_absurd)
  case proj_merge s L1 L2 =>
    cases s <;> (apply! Subset.proj_merge)
  case trans ha hb => apply! Subset.trans

theorem CaptureSet.cweaken_def {C : CaptureSet n k} :
  C.cweaken = C.crename FinFun.weaken := by
  induction C <;> aesop

-- /-!
-- ## Projections
-- -/

theorem CaptureSet.Subset.proj (hsub : Subset C D) : Subset (C.proj K) (D.proj K) := by
  induction hsub <;> try simp
  case empty => apply empty
  case rfl => apply rfl
  case union_l ha hb => apply! union_l
  case union_rl ha => apply! union_rl
  case union_rr hb => apply! union_rr
  case singleton_subkind hs =>
    apply singleton_subkind $ Kind.Intersect.with_subkind_r hs
  case singleton_absurd he =>
    apply trans (.singleton_subkind _) (.singleton_absurd he)
    apply Kind.Intersect.subkind_l
  case proj_merge => apply proj_merge
  case trans ha hb => apply! trans

theorem CaptureSet.proj_rename {C : CaptureSet n k} : (C.proj K).rename f = (C.rename f).proj K := by
  induction C
  case empty => simp
  case singleton => simp
  case union ha hb => simp; aesop

theorem CaptureSet.proj_crename {C : CaptureSet n k} : (C.proj K).crename f = (C.crename f).proj K := by
  induction C
  case empty => simp
  case singleton => simp
  case union ha hb => simp; aesop

theorem CaptureSet.proj_weaken {C : CaptureSet n k} : (C.proj K).weaken = (C.weaken).proj K := C.proj_rename
theorem CaptureSet.proj_cweaken {C : CaptureSet n k} : (C.proj K).cweaken = (C.cweaken).proj K := C.proj_crename

theorem CaptureSet.Subset.proj_l : Subset (C.proj K) C := by
  induction C
  case empty => constructor
  case union ha hb => simp; apply! union_monotone
  case singleton => apply singleton_subkind; apply Kind.Intersect.subkind_l

theorem CaptureSet.Subset.proj_proj_intersect {C : CaptureSet n k}: Subset ((C.proj K).proj L) (C.proj (K.intersect L)) := by
  induction C
  case empty => simp; constructor
  case union ha hb => simp; apply! union_monotone
  case singleton =>
    apply singleton_subkind
    apply Kind.Intersect.assoc_subkind

theorem CaptureSet.Subset.proj_intersect_proj {C : CaptureSet n k}: Subset (C.proj (K.intersect L)) ((C.proj K).proj L) := by
  induction C
  case empty => simp; constructor
  case union ha hb => simp; apply! union_monotone
  case singleton =>
    apply singleton_subkind
    apply Kind.Intersect.assoc_superkind
