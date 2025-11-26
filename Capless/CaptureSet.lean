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
def CaptureSet.depth : CaptureSet n k -> Nat
  | empty => 0
  | union a b => 1 + max a.depth b.depth
  | singleton _ => 1
  | csingleton _ => 1
  | proj c _ => 1 + c.depth

@[simp]
instance : EmptyCollection (CaptureSet n k) where
  emptyCollection := CaptureSet.empty

notation:max "{x=" x "}" => CaptureSet.singleton x
notation:max "{c=" c "}" => CaptureSet.csingleton c

@[simp]
instance : Union (CaptureSet n k) where
  union := CaptureSet.union

/-- Subset relation on capture sets. -/
inductive CaptureSet.Subset : Nat -> CaptureSet n k → CaptureSet n k → Prop where
| empty : Subset 0 {} C
| rfl : Subset 0 C C
| union_l :
  Subset a C1 C ->
  Subset b C2 C ->
  Subset (1 + a + b) (C1 ∪ C2) C
| union_rl :
  Subset a C C1 ->
  Subset (1 + a) C (C1 ∪ C2)
| union_rr :
  Subset a C C2 ->
  Subset (1 + a) C (C1 ∪ C2)
| trans : Subset a C1 C2 -> Subset b C2 C3 -> Subset (1 + a + b) C1 C3
/- projection distributivity -/
| proj_empty : Subset 0 (.proj .empty K) .empty
| proj_union_l : Subset 0 (.union (.proj C1 K) (.proj C2 K)) (.proj (C1 ∪ C2) K)
| proj_union_r : Subset 0 (.proj (C1 ∪ C2) K) (.union (.proj C1 K) (.proj C2 K))
| proj : Subset a C D -> Subset (1 + a) (.proj C K) (.proj D K)

@[simp]
instance : HasSubset (CaptureSet n k) where
  Subset A B := ∃ n: Nat, CaptureSet.Subset n A B

/- Existentialification -/

theorem CaptureSet.Subset.empty' : CaptureSet.empty ⊆ C := by exists 0; apply empty
theorem CaptureSet.Subset.rfl' {C : CaptureSet n k} : C ⊆ C := by exists 0; apply rfl
theorem CaptureSet.Subset.union_l' {C1 C2 C : CaptureSet n k} (h1 : C1 ⊆ C) (h2 : C2 ⊆ C) : (C1 ∪ C2) ⊆ C := by
  have ⟨n1, _⟩ := h1
  have ⟨n2, _⟩ := h2
  exists 1 + n1 + n2; apply! union_l
theorem CaptureSet.Subset.union_rl' {C1 C2 C : CaptureSet n k} (h1 : C ⊆ C1) : C ⊆ (C1 ∪ C2) := by
  have ⟨n1, _⟩ := h1
  exists 1 + n1; apply! union_rl
theorem CaptureSet.Subset.union_rr' {C1 C2 C : CaptureSet n k} (h1 : C ⊆ C2) : C ⊆ (C1 ∪ C2) := by
  have ⟨n1, _⟩ := h1
  exists 1 + n1; apply! union_rr
theorem CaptureSet.Subset.trans' {C1 C2 C3 : CaptureSet n k} (h1 : C1 ⊆ C2) (h2 : C2 ⊆ C3) : C1 ⊆ C3 := by
  have ⟨n1, _⟩ := h1
  have ⟨n2, _⟩ := h2
  exists 1 + n1 + n2; apply! trans
theorem CaptureSet.Subset.proj_empty' : (CaptureSet.proj CaptureSet.empty K : CaptureSet n k) ⊆ CaptureSet.empty := by
  exists 0; apply proj_empty
theorem CaptureSet.Subset.proj_union_l' {C1 C2 : CaptureSet n k} : (CaptureSet.union (CaptureSet.proj C1 K) (CaptureSet.proj C2 K)) ⊆ (CaptureSet.proj (C1 ∪ C2) K) := by
  exists 0; apply proj_union_l
theorem CaptureSet.Subset.proj_union_r' {C1 C2 : CaptureSet n k} : (CaptureSet.proj (C1 ∪ C2) K) ⊆ (CaptureSet.union (CaptureSet.proj C1 K) (CaptureSet.proj C2 K)) := by
  exists 0; apply proj_union_r
theorem CaptureSet.Subset.proj' {C D : CaptureSet n k} (h : C ⊆ D) : (CaptureSet.proj C K) ⊆ (CaptureSet.proj D K) := by
  have ⟨n1, _⟩ := h
  exists 1 + n1; apply! proj



@[simp]
instance : IsTrans (CaptureSet n k) (HasSubset.Subset) where
  trans a b c ha hb := by
    have ⟨a, ha⟩ := ha
    have ⟨b, hb⟩ := hb
    exists (1 + a + b)
    apply CaptureSet.Subset.trans ha hb

theorem CaptureSet.Subset.union_l_inv {C1 C2 C3 : CaptureSet n k} (h1' : (C1 ∪ C2) ⊆ C3) : (C1 ⊆ C3) ∧ (C2 ⊆ C3) := by
  generalize h0 : C1 ∪ C2 = C at h1'
  have ⟨n, h1⟩ := h1'
  induction h1 generalizing C1 C2 <;> (subst_vars; simp_all)
  case rfl =>
    apply And.intro
    apply Exists.intro 1 $ union_rl .rfl
    apply Exists.intro 1 $ union_rr .rfl
  case union_l a _ _ b _ h1 h2 ih1 ih2 =>
    apply And.intro
    exists a
    exists b
  case union_rl ha ih =>
    have ⟨⟨l, hl⟩, r, hr⟩ := ih _ ha
    apply And.intro
    apply Exists.intro (1 + l) $ .union_rl hl
    apply Exists.intro (1 + r) $ .union_rl hr
  case union_rr ha ih =>
    have ⟨⟨l, hl⟩, r, hr⟩ := ih _ ha
    apply And.intro
    apply Exists.intro (1 + l) $ .union_rr hl
    apply Exists.intro (1 + r) $ .union_rr hr
  case trans b _ h1 _ h2 ih2 =>
    have ⟨⟨l, hl⟩, r, hr⟩ := ih2 _ h2
    apply And.intro
    exists (1 + l + b); apply trans hl h1
    exists (1 + r + b); apply trans hr h1
  case proj_union_l =>
    have ⟨_, _⟩ := h0
    subst_vars; simp_all
    apply And.intro
    exists 1 + 1; apply proj; apply union_rl .rfl
    exists 1 + 1; apply proj; apply union_rr .rfl

theorem CaptureSet.Subset.proj_union_l_inv {C1 C2 C3 : CaptureSet n k} (h1' : (.proj (C1 ∪ C2) K) ⊆ C3) : ((C1.proj K) ⊆ C3) ∧ ((C2.proj K) ⊆ C3) := by
  generalize h0 : (C1 ∪ C2).proj K = C at h1'
  have ⟨n, h1⟩ := h1'
  induction h1 generalizing C1 C2 <;> (subst_vars; simp_all)
  case rfl =>
    apply And.intro
    exists 1 + 1; apply proj $ union_rl .rfl
    exists 1 + 1; apply proj $ union_rr .rfl
  case union_rl ha ih =>
    have ⟨⟨l, hl⟩, r, hr⟩ := ih _ ha
    apply And.intro
    exists 1 + l; apply! union_rl
    exists 1 + r; apply! union_rl
  case union_rr ha ih =>
    have ⟨⟨l, hl⟩, r, hr⟩ := ih _ ha
    apply And.intro
    exists 1 + l; apply! union_rr
    exists 1 + r; apply! union_rr
  case trans b _ ha hb iha ihb =>
    have ⟨⟨l, hl⟩, r, hr⟩ := ihb _ iha
    apply And.intro
    exists (1 + l + b); apply! trans
    exists (1 + r + b); apply! trans
  case proj_union_r =>
    have ⟨⟨_, _⟩, _⟩ := h0
    subst_vars; simp_all
    apply And.intro
    exists 1; apply union_rl .rfl
    exists 1; apply union_rr .rfl
  case proj ha ih =>
    have ⟨_, _⟩ := h0
    subst_vars; simp_all
    have ⟨⟨l, hl⟩, r, hr⟩ := union_l_inv $ Exists.intro _ ha
    apply And.intro
    exists 1 + l; apply! proj
    exists 1 + r; apply! proj

theorem CaptureSet.Subset.union_monotone {C1 C2 D1 D2 : CaptureSet n k} (hc : C1 ⊆ C2) (hd : D1 ⊆ D2) : (C1 ∪ D1) ⊆ (C2 ∪ D2) := by
  have ⟨n1, hc1⟩ := hc
  have ⟨n2, hc2⟩ := hd
  exists 1 + (1 + n1) + (1 + n2)
  apply union_l
  apply! union_rl
  apply! union_rr

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
  C ⊆ C := by exists 0; constructor

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
  (h' : C1 ⊆ C2) :
  C1.crename f ⊆ C2.crename f := by
  have ⟨n, h⟩ := h'
  induction h <;> simp
  case empty => exists 0; constructor
  case rfl => exists 0; constructor
  case proj_empty => exists 0; constructor
  case proj_union_l => exists 0; constructor
  case proj_union_r => exists 0; apply Subset.proj_union_r
  case union_l ha hb iha ihb =>
    have ⟨l, hl⟩ := iha $ Exists.intro _ ha
    have ⟨r, hr⟩ := ihb $ Exists.intro _ hb
    exists 1 + l + r
    apply! Subset.union_l
  case union_rl ha ih =>
    have ⟨l, hl⟩ := ih $ Exists.intro _ ha
    exists 1 + l
    apply! Subset.union_rl
  case union_rr ha ih =>
    have ⟨l, hl⟩ := ih $ Exists.intro _ ha
    exists 1 + l
    apply! Subset.union_rr
  case trans ha hb iha ihb =>
    have ⟨l, hl⟩ := iha $ Exists.intro _ ha
    have ⟨r, hr⟩ := ihb $ Exists.intro _ hb
    exists 1 + l + r
    apply! Subset.trans
  case proj ha ih =>
    have ⟨l, hl⟩ := ih $ Exists.intro _ ha
    exists 1 + l
    apply! Subset.proj

theorem CaptureSet.cweaken_monotone {C1 C2 : CaptureSet n k}
  (h' : C1 ⊆ C2) :
  C1.cweaken ⊆ C2.cweaken := by
  have ⟨n, h⟩ := h'
  induction h <;> simp
  case empty => exists 0; constructor
  case rfl => exists 0; constructor
  case proj_empty => exists 0; constructor
  case proj_union_l => exists 0; constructor
  case proj_union_r => exists 0; apply Subset.proj_union_r
  case union_l ha hb iha ihb =>
    have ⟨l, hl⟩ := iha $ Exists.intro _ ha
    have ⟨r, hr⟩ := ihb $ Exists.intro _ hb
    exists 1 + l + r
    apply! Subset.union_l
  case union_rl ha ih =>
    have ⟨l, hl⟩ := ih $ Exists.intro _ ha
    exists 1 + l
    apply! Subset.union_rl
  case union_rr ha ih =>
    have ⟨l, hl⟩ := ih $ Exists.intro _ ha
    exists 1 + l
    apply! Subset.union_rr
  case trans ha hb iha ihb =>
    have ⟨l, hl⟩ := iha $ Exists.intro _ ha
    have ⟨r, hr⟩ := ihb $ Exists.intro _ hb
    exists 1 + l + r
    apply! Subset.trans
  case proj ha ih =>
    have ⟨l, hl⟩ := ih $ Exists.intro _ ha
    exists 1 + l
    apply! Subset.proj

theorem CaptureSet.cweaken_def {C : CaptureSet n k} :
  C.cweaken = C.crename FinFun.weaken := by
  induction C <;> aesop

/-!
## Projections
-/

inductive ProjectedSingleton: CaptureSet n k -> (CaptureSet n k) -> Prop where
  | var : ProjectedSingleton {x=x} {x=x}
  | cvar : ProjectedSingleton {c=c} {c=c}
  | proj : ProjectedSingleton s C -> ProjectedSingleton s (.proj C K)

inductive ProjectedSingletonWith : (CaptureSet n k) -> (K : Kind) -> (CaptureSet n k) -> Prop where
  | here : ProjectedSingleton s C -> ProjectedSingletonWith s K (.proj C K)
  | there : ProjectedSingletonWith s K C -> ProjectedSingletonWith s K (.proj C K')

def ProjectedSingletonWith.erase (hp : ProjectedSingletonWith s K C) : ProjectedSingleton s C := by
  induction hp <;> apply! ProjectedSingleton.proj

/-- A capture set that only has projections on top of singletons. -/
inductive ProjectedSingletonsOnly: CaptureSet n k -> Prop where
  | empty : ProjectedSingletonsOnly .empty
  | singleton : ProjectedSingleton s C -> ProjectedSingletonsOnly C
  | union : ProjectedSingletonsOnly C1 -> ProjectedSingletonsOnly C2 -> ProjectedSingletonsOnly (.union C1 C2)

@[simp]
def CaptureSet.push_proj (C: CaptureSet n k) (K: Kind) : CaptureSet n k :=
  match C with
  | .empty => .empty
  | .singleton c => proj (.singleton c) K
  | .csingleton c => proj (.csingleton c) K
  | .proj C1 K1 => proj (.proj C1 K1) K
  | .union C1 C2 => .union (C1.push_proj K) (C2.push_proj K)

@[simp]
def CaptureSet.canonicalize (C : CaptureSet n k) : CaptureSet n k :=
  match C with
  | .empty => .empty
  | .singleton c => .singleton c
  | .csingleton c => .csingleton c
  | .union C1 C2 => .union (C1.canonicalize) (C2.canonicalize)
  | .proj C1 K => C1.canonicalize.push_proj K

theorem CaptureSet.push_proj_is_superset (C : CaptureSet n k) : (C.proj K) ⊆ C.push_proj K := by
  induction C <;> simp only [push_proj]
  case empty => exists 0; apply Subset.proj_empty
  case union C1 C2 ih1 ih2 =>
    apply IsTrans.trans (r := HasSubset.Subset)
    exists 0; apply Subset.proj_union_r
    apply! Subset.union_monotone
  case singleton => exists 0; apply Subset.rfl
  case csingleton => exists 0; apply Subset.rfl
  case proj => apply Subset.proj' Subset.rfl'

theorem CaptureSet.canonicalize_is_superset {C : CaptureSet n k} : C ⊆ C.canonicalize := by
  induction C <;> (simp; try apply Subset.rfl')
  case union ih1 ih2 => apply Subset.union_monotone ih1 ih2
  case proj C1 K ih =>
    apply Subset.trans'
    apply Subset.proj' ih
    apply push_proj_is_superset

theorem CaptureSet.push_proj_is_subset {C : CaptureSet n k} : C.push_proj K ⊆ C.proj K := by
  induction C <;> (simp; try apply Subset.rfl')
  case empty => apply Subset.empty'
  case union C1 C2 ih1 ih2 =>
    apply Subset.trans' _ Subset.proj_union_l'
    apply! Subset.union_monotone

theorem CaptureSet.canonicalize_is_subset {C : CaptureSet n k} : C.canonicalize ⊆ C := by
  induction C <;> (simp; try apply Subset.rfl')
  case union ih1 ih2 => apply Subset.union_monotone ih1 ih2
  case proj C1 K ih =>
    apply Subset.trans' C1.canonicalize.push_proj_is_subset
    apply Subset.proj' ih

theorem CaptureSet.push_proj_singleton {C : CaptureSet n k} (hp: ProjectedSingletonsOnly C) : ProjectedSingletonsOnly (C.push_proj K) := by
  induction hp <;> try simp_all
  case empty => constructor
  case singleton hp =>
    induction hp
    case var => apply ProjectedSingletonsOnly.singleton (.proj .var)
    case cvar => apply ProjectedSingletonsOnly.singleton (.proj .cvar)
    case proj =>
      apply ProjectedSingletonsOnly.singleton
      apply ProjectedSingleton.proj
      apply! ProjectedSingleton.proj
  case union C1 C2 ih1 ih2 =>
    apply! ProjectedSingletonsOnly.union

theorem CaptureSet.canonicalize_is_projected_singletons_only {C : CaptureSet n k} : ProjectedSingletonsOnly C.canonicalize := by
  induction C <;> try simp
  case empty => apply ProjectedSingletonsOnly.empty
  case singleton => apply ProjectedSingletonsOnly.singleton .var
  case csingleton => apply ProjectedSingletonsOnly.singleton .cvar
  case union C1 C2 ih1 ih2 => apply ProjectedSingletonsOnly.union ih1 ih2
  case proj C K ih =>
    apply push_proj_singleton
    assumption

lemma CaptureSet.push_proj_depth {C : CaptureSet n k} : (C.push_proj K).depth ≤ 1 + C.depth := by
  induction C <;> simp; omega

theorem CaptureSet.canonicalize_depth {C : CaptureSet n k} : C.canonicalize.depth ≤ C.depth := by
  induction C <;> simp
  case union ih1 ih2 => omega
  case proj C K ih =>
    apply IsTrans.trans
    apply C.canonicalize.push_proj_depth
    simp; exact ih

lemma CaptureSet.push_proj_singleton_eq {C : CaptureSet n k} (hp : ProjectedSingleton s C) : (C.push_proj K) = (C.proj K) := by
  induction hp <;> simp

theorem CaptureSet.canonicalize_projected_singletons {C : CaptureSet n k} (hp : ProjectedSingletonsOnly C) : C.canonicalize = C := by
  induction hp
  case singleton s C hs =>
    induction hs <;> simp
    case proj ha ih =>
      rw [ih]
      apply! push_proj_singleton_eq
  case empty => simp
  case union ha hb iha ihb =>
    simp; aesop

theorem CaptureSet.canonicalize_idempt {C : CaptureSet n k} : C.canonicalize.canonicalize = C.canonicalize := by
  have h := C.canonicalize_is_projected_singletons_only
  rw [C.canonicalize.canonicalize_projected_singletons h]

theorem CaptureSet.Subset.canonicalize {A B : CaptureSet n k} (hs : A ⊆ B) : A.canonicalize ⊆ B.canonicalize := by
  apply trans'
  apply A.canonicalize_is_subset
  apply trans' hs
  apply B.canonicalize_is_superset


inductive HasSingleton : CaptureSet n k -> CaptureSet n k -> Prop where
  | var : HasSingleton {x=x} {x=x}
  | cvar : HasSingleton {c=c} {c=c}
  | union_l : HasSingleton s C1 -> HasSingleton s (.union C1 C2)
  | union_r : HasSingleton s C2 -> HasSingleton s (.union C1 C2)
  | proj : HasSingleton s C -> HasSingleton (s.proj K) (C.proj K)

theorem CaptureSet.Subset.subset_has_singleton' {C1 C2 : CaptureSet n k} (hh1 : HasSingleton s C1) (hs : Subset t C1 C2) : HasSingleton s C2 := by
  induction hs generalizing s
  case empty => cases hh1
  case rfl => assumption
  case union_l ih1 ih2 =>
    cases hh1
    apply! ih1
    apply! ih2
  case union_rl ih => apply HasSingleton.union_l; apply ih hh1
  case union_rr ih => apply HasSingleton.union_r; apply ih hh1
  case trans ha hb iha ihb =>
    apply ihb $ iha hh1
  case proj_empty => cases hh1; rename_i hh1; cases hh1
  case proj_union_l =>
    cases hh1
    { rename_i hh1; cases hh1; constructor; apply! HasSingleton.union_l }
    { rename_i hh1; cases hh1; constructor; apply! HasSingleton.union_r }
  case proj_union_r =>
    cases hh1
    rename_i hh1
    cases hh1
    { apply HasSingleton.union_l; constructor; assumption }
    { apply HasSingleton.union_r; constructor; assumption }
  case proj ih =>
    cases hh1
    constructor
    apply! ih

theorem CaptureSet.subset_has_singleton {C1 C2 : CaptureSet n k} (hs : C1 ⊆ C2) (hh : HasSingleton C C1) : HasSingleton C C2 := by
  have ⟨_, h⟩ := hs
  apply Subset.subset_has_singleton' hh h

theorem CaptureSet.projected_singleton_has_singleton (hp : ProjectedSingleton s C) : HasSingleton C C := by
  induction hp
  case var => constructor
  case cvar => constructor
  case proj hp => constructor; assumption

theorem CaptureSet.projected_singleton_unique_singleton (hp : ProjectedSingleton s C) (hh : HasSingleton C' C) : C' = C := by
  induction hp generalizing C'
  case var => cases hh; rfl
  case cvar => cases hh; rfl
  case proj hp ih =>
    cases hh
    rename_i hh
    have ih1 := ih hh
    subst_vars
    simp


theorem CaptureSet.Subset.empty_projected_singleton {C : CaptureSet n k} (hs : C ⊆ .empty) (hp : ProjectedSingleton s C) : False := by
  have ⟨n, h⟩ := hs
  have h2 := CaptureSet.Subset.subset_has_singleton' (projected_singleton_has_singleton hp) h
  cases h2

end Capless
