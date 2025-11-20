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
| singleton : Fin n -> CaptureSet n k
| csingleton : Fin k -> CaptureSet n k
| proj : CaptureSet n k -> Kind -> CaptureSet n k

@[simp]
instance : EmptyCollection (CaptureSet n k) where
  emptyCollection := CaptureSet.empty

notation:max "{x=" x "}" => CaptureSet.singleton x
notation:max "{c=" c "}" => CaptureSet.csingleton c
notation:max "{s=" s "}" => CaptureSet.singleton s

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
| trans : Subset C1 C2 -> Subset C2 C3 -> Subset C1 C3
/- projection distributivity -/
| proj_empty : Subset (.proj .empty K) .empty
| proj_union_l : Subset (.union (.proj C1 K) (.proj C2 K)) (.proj (C1 ∪ C2) K)
| proj_union_r : Subset (.proj (C1 ∪ C2) K) (.union (.proj C1 K) (.proj C2 K))
| proj_proj : Subset (.proj (.proj C K1) K2) (.proj (.proj C K2) K1) -- allows us to consider only the relevant projection
| proj_l : Subset (.proj C K) C -- allows introducing projections anywhere
| proj : Subset C D -> Subset (.proj C K) (.proj D K)

theorem CaptureSet.Subset.union_l_inv (h1 : Subset (C1 ∪ C2) C3) : (Subset C1 C3) ∧ (Subset C2 C3) := by
  generalize h0 : C1 ∪ C2 = C at h1
  induction h1 generalizing C1 C2 <;> (subst_vars; simp_all)
  case rfl =>
    apply And.intro
    apply union_rl .rfl
    apply union_rr .rfl
  case union_rl ha ih =>
    have ⟨hl, hr⟩ := ih
    apply And.intro <;> (apply union_rl; assumption)
  case union_rr ha ih =>
    have ⟨hl, hr⟩ := ih
    apply And.intro <;> (apply union_rr; assumption)
  case trans h1 h2 ih1 ih2 =>
    have ⟨_, _⟩ := ih2
    apply And.intro <;> apply! trans _ h1
  case proj_union_l =>
    have ⟨_, _⟩ := h0
    subst_vars; simp_all
    apply And.intro <;> apply proj
    apply union_rl .rfl
    apply union_rr .rfl

theorem CaptureSet.Subset.proj_union_l_inv (h1 : Subset (.proj (C1 ∪ C2) K)  C3) : (Subset (C1.proj K) C3) ∧ (Subset (C2.proj K) C3) := by
  generalize h0 : (C1 ∪ C2).proj K = C at h1
  induction h1 generalizing C1 C2 <;> (subst_vars; simp_all)
  case rfl =>
    apply And.intro <;> apply proj
    apply union_rl .rfl
    apply union_rr .rfl
  case union_rl ha ih =>
    have ⟨hl, hr⟩ := ih
    apply And.intro <;> (apply union_rl; assumption)
  case union_rr ha ih =>
    have ⟨hl, hr⟩ := ih
    apply And.intro <;> (apply union_rr; assumption)
  case trans ha hb iha ihb =>
    have ⟨_, _⟩ := ihb
    apply And.intro <;> apply! trans
  case proj_union_r =>
    have ⟨⟨_, _⟩, _⟩ := h0
    subst_vars; simp_all
    apply And.intro
    apply union_rl .rfl
    apply union_rr .rfl
  case proj_l =>
    have ⟨_, _⟩ := h0
    subst_vars; simp_all
    apply And.intro
    apply union_rl .proj_l
    apply union_rr .proj_l
  case proj ha ih =>
    have ⟨_, _⟩ := h0
    subst_vars; simp_all
    have ⟨_, _⟩ := ha.union_l_inv
    apply And.intro <;> apply! proj

theorem CaptureSet.Subset.union_monotone (hc : Subset C1 C2) (hd : Subset D1 D2) : Subset (C1 ∪ D1) (C2 ∪ D2) := by
  apply union_l
  apply! union_rl
  apply! union_rr

@[simp]
instance : HasSubset (CaptureSet n k) where
  Subset := CaptureSet.Subset

@[simp]
instance : IsTrans (CaptureSet n k) Subset where
  trans a b c ha hb := CaptureSet.Subset.trans ha hb

/-!
## Renaming operations
-/

@[simp]
def CaptureSet.rename (C : CaptureSet n k) (f : FinFun n n') : CaptureSet n' k :=
  match C with
  | empty => empty
  | union C1 C2 => (C1.rename f) ∪ (C2.rename f)
  | singleton x => singleton $ f x
  | csingleton c => csingleton c
  | proj c k => (c.rename f).proj k

@[simp]
def CaptureSet.crename (C : CaptureSet n k) (f : FinFun k k') : CaptureSet n k' :=
  match C with
  | empty => empty
  | union C1 C2 => (C1.crename f) ∪ (C2.crename f)
  | singleton x => singleton x
  | csingleton c => csingleton $ f c
  | proj c k => (c.crename f).proj k

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
  case proj_empty => simp; apply! Subset.proj_empty
  case proj_union_l => simp; apply! Subset.proj_union_l
  case proj_union_r => simp; apply! Subset.proj_union_r
  case proj_proj => simp; apply! Subset.proj_proj
  case proj_l => simp; apply! Subset.proj_l
  case proj => simp; apply! Subset.proj


theorem CaptureSet.cweaken_monotone {C1 C2 : CaptureSet n k}
  (h : C1 ⊆ C2) :
  C1.cweaken ⊆ C2.cweaken := by
  induction h <;> try (solve | constructor | simp; constructor <;> trivial)
  case union_rr =>
    simp
    apply! Subset.union_rr
  case proj_empty => simp; apply! Subset.proj_empty
  case proj_union_l => simp; apply! Subset.proj_union_l
  case proj_union_r => simp; apply! Subset.proj_union_r
  case proj_proj => simp; apply! Subset.proj_proj
  case proj_l => simp; apply! Subset.proj_l
  case proj => simp; apply! Subset.proj

theorem CaptureSet.cweaken_def {C : CaptureSet n k} :
  C.cweaken = C.crename FinFun.weaken := by
  induction C <;> aesop

/-!
## Projections
-/

/-- A capture set that only has projections on top of singletons. -/
inductive ProjectedSingletonsOnly: (isSingleton : Bool) -> CaptureSet n k -> Prop where
  | empty : ProjectedSingletonsOnly false (.empty)
  | singleton : ProjectedSingletonsOnly true (.singleton s)
  | csingleton : ProjectedSingletonsOnly true (.csingleton s)
  | proj : ProjectedSingletonsOnly true C -> ProjectedSingletonsOnly true (C.proj K)
  | union : ProjectedSingletonsOnly a C1 -> ProjectedSingletonsOnly b C2 -> ProjectedSingletonsOnly false (.union C1 C2)

theorem CaptureSet.push_projection_down (h1 : ProjectedSingletonsOnly a C) : ∃ C1, ProjectedSingletonsOnly a C1 ∧ C1 ⊆ (C.proj K) ∧ (C.proj K) ⊆ C1 := by
  induction h1 generalizing K
  case union ha hb iha ihb =>
    have ⟨Ca, ha1, ha2, ha3⟩ := iha (K:=K)
    have ⟨Cb, hb1, hb2, hb3⟩ := ihb (K:=K)
    exists (.union Ca Cb)
    apply And.intro
    apply! ProjectedSingletonsOnly.union
    apply And.intro
    apply Subset.trans _ .proj_union_l
    apply Subset.union_monotone ha2 hb2
    apply Subset.trans .proj_union_r _
    apply! Subset.union_monotone
  case proj C K2 ha iha =>
    have ⟨Ca, ha1, ha2, ha3⟩ := iha (K:=K2)
    exists Ca.proj K
    apply And.intro
    apply! ProjectedSingletonsOnly.proj
    apply And.intro <;> apply! Subset.proj
  case empty =>
    exists .empty
    apply And.intro .empty
    apply And.intro .empty .proj_empty
  case singleton n =>
    exists (.proj (.singleton n) K)
    apply And.intro (.proj .singleton)
    apply And.intro <;> apply Subset.rfl
  case csingleton n =>
    exists (.proj (.csingleton n) K)
    apply And.intro (.proj .csingleton)
    apply And.intro <;> apply Subset.rfl

/-- There always exists a capture set equivalent to the given C, whose projections are only on top of singletons. -/
theorem CaptureSet.exists_projected_singleton_only (C : CaptureSet n k) : ∃ C1 a, ProjectedSingletonsOnly a C1 ∧ C1 ⊆ C ∧ C ⊆ C1 := by
  induction C
  case empty =>
    exists .empty, false
    apply And.intro
    apply ProjectedSingletonsOnly.empty
    apply And.intro <;> apply Subset.rfl
  case union a b ha hb =>
    have ⟨Ca, _, ha1, ha2, ha3⟩ := ha
    have ⟨Cb, _, hb1, hb2, hb3⟩ := hb
    exists (.union Ca Cb), false
    apply And.intro
    apply! ProjectedSingletonsOnly.union
    apply And.intro <;> apply! Subset.union_monotone
  case singleton n =>
    exists .singleton n, true
    apply And.intro ProjectedSingletonsOnly.singleton
    apply And.intro <;> apply Subset.rfl
  case csingleton k =>
    exists .csingleton k, true
    apply And.intro ProjectedSingletonsOnly.csingleton
    apply And.intro <;> apply Subset.rfl
  case proj C K ih =>
    have ⟨Ca, a, ha1, ha2, ha3⟩ := ih
    have ⟨Cb, hb1, hb2, hb3⟩ := CaptureSet.push_projection_down ha1 (K:=K)
    exists Cb, a
    apply And.intro hb1
    apply And.intro
    apply Subset.trans hb2 (.proj ha2)
    apply Subset.trans (.proj ha3) hb3
end Capless
