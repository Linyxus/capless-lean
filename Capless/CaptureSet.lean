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
| proj : Singleton n k -> Kind -> Singleton n k

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
| singleton : Singleton n k -> CaptureSet n k

@[simp]
def CaptureSet.proj (c : CaptureSet n k) (K : Kind) :=
  match c with
  | empty => empty
  | union c1 c2 => union (c1.proj K) (c2.proj K)
  | singleton s => singleton $ s.proj K

@[simp]
instance : EmptyCollection (CaptureSet n k) where
  emptyCollection := CaptureSet.empty

notation:max "{x=" x "}" => CaptureSet.singleton (Singleton.var x)
notation:max "{c=" c "}" => CaptureSet.singleton (Singleton.cvar c)

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

theorem CaptureSet.Subset.union_l_inv (hs : Subset (.union a1 a2) b) : Subset a1 b ∧ Subset a2 b := by
  cases hs
  case rfl =>
    apply And.intro
    apply union_rl .rfl
    apply union_rr .rfl
  case union_l => apply! And.intro
  case union_rl ha =>
    have ⟨_, _⟩ := ha.union_l_inv
    apply And.intro <;> apply! union_rl
  case union_rr ha =>
    have ⟨_, _⟩ := ha.union_l_inv
    apply And.intro <;> apply! union_rr

theorem CaptureSet.Subset.trans (hs1 : Subset a b) (hs2 : Subset b c) : Subset a c := by
  induction hs1
  case empty => constructor
  case rfl => assumption
  case union_l ha hb iha ihb =>
    apply! union_l (iha _) (ihb _)
  case union_rl ha iha =>
    have ⟨_, _⟩ := hs2.union_l_inv
    apply! iha
  case union_rr ha iha =>
    have ⟨_, _⟩ := hs2.union_l_inv
    apply! iha


@[simp]
instance : IsTrans (CaptureSet n k) (HasSubset.Subset) where
  trans a b c := CaptureSet.Subset.trans

theorem CaptureSet.Subset.union_monotone {C1 C2 D1 D2 : CaptureSet n k} (hc : Subset C1 C2) (hd : Subset D1 D2) : Subset (C1 ∪ D1) (C2 ∪ D2) := by
  apply union_l
  apply! union_rl
  apply! union_rr

/-!
## Renaming operations
-/

@[simp]
def Singleton.rename (s : Singleton n k) (f : FinFun n n') : Singleton n' k :=
  match s with
  | var n => var $ f n
  | cvar k => cvar k
  | proj s K => (s.rename f).proj K

@[simp]
def Singleton.crename (s : Singleton n k) (f : FinFun k k') : Singleton n k' :=
  match s with
  | var n => var n
  | cvar k => cvar $ f k
  | proj s K => (s.crename f).proj K

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
  | singleton s => singleton $ s.rename f

@[simp]
def CaptureSet.crename (C : CaptureSet n k) (f : FinFun k k') : CaptureSet n k' :=
  match C with
  | empty => empty
  | union C1 C2 => (C1.crename f) ∪ (C2.crename f)
  | singleton s => singleton $ s.crename f

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
  induction h <;> simp
  case empty => constructor
  case rfl => constructor
  case union_l ha hb iha ihb =>
    apply! Subset.union_l
  case union_rl ha ih =>
    apply! Subset.union_rl
  case union_rr ha ih =>
    apply! Subset.union_rr

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

theorem CaptureSet.cweaken_def {C : CaptureSet n k} :
  C.cweaken = C.crename FinFun.weaken := by
  induction C <;> aesop

-- /-!
-- ## Projections
-- -/

-- `n` with projections widen `C'` to given `C`
inductive WidenVar : Fin n -> Singleton n k -> CaptureSet n k -> CaptureSet n k -> Prop where
  | var : WidenVar n (.var n) C C
  | proj : WidenVar n s C' C -> WidenVar n (s.proj K) C' (C.proj K)

-- `n` with projections widen to given `C`, including a projection to `K`
inductive WidenVarWith : Fin n -> Singleton n k -> CaptureSet n k -> CaptureSet n k -> Kind -> Prop where
  | here : WidenVar n s C' C -> WidenVarWith n (s.proj K) C' (C.proj K) K
  | there : WidenVarWith n s C' C K -> WidenVarWith n (s.proj K') C' (C.proj K') K

-- `k` with projections widen `C'` to given `C`
inductive WidenCVar : Fin k -> Singleton k k -> CaptureSet k k -> CaptureSet k k -> Prop where
  | var : WidenCVar k (.cvar k) C C
  | proj : WidenCVar k s C' C -> WidenCVar k (s.proj K) C' (C.proj K)

-- `k` with projections widen to given `C`, including a projection to `K`
inductive WidenCVarWith : Fin k -> Singleton k k -> CaptureSet k k -> CaptureSet k k -> Kind -> Prop where
  | here : WidenCVar k s C' C -> WidenCVarWith k (s.proj K) C' (C.proj K) K
  | there : WidenCVarWith k s C' C K -> WidenCVarWith k (s.proj K') C' (C.proj K') K

inductive Singleton.IsVar : Singleton n k -> Fin n -> Prop where
  | var : IsVar (.var n) n
  | proj : IsVar s n -> IsVar (s.proj K) n

theorem Singleton.IsVar.proj_inv (hv : IsVar (s.proj K) n) : IsVar s n := by cases hv; assumption

theorem WidenVar.is_var (hw : WidenVar n s C' C) : s.IsVar n := by
  induction hw
  case var => constructor
  case proj ih => apply ih.proj

inductive Singleton.IsVarWith : Singleton n k -> Fin n -> Kind -> Prop where
  | here : IsVar s n -> IsVarWith (s.proj K) n K
  | there : IsVarWith s n K -> IsVarWith (s.proj K') n K

theorem WidenVarWith.is_var_with (hw : WidenVarWith k s C' C K) : s.IsVarWith k K := by
  induction hw
  case here hw => apply Singleton.IsVarWith.here hw.is_var
  case there ih => apply ih.there

inductive Singleton.IsCVar : Singleton n k -> Fin k -> Prop where
  | var : IsCVar (.cvar n) n
  | proj : IsCVar s n -> IsCVar (s.proj K) n

theorem Singleton.IsCVar.proj_inv (hv : IsCVar (s.proj K) n) : IsCVar s n := by cases hv; assumption

theorem WidenCVar.is_cvar (hw : WidenCVar n s C' C) : s.IsCVar n := by
  induction hw
  case var => constructor
  case proj ih => apply ih.proj


-- inductive HasSingleton : Singleton n k -> Singleton n k -> Prop where
--   | var : HasSingleton (.var n) (.var n)
--   | cvar : HasSingleton (.cvar k) (.cvar k)
--   | proj : HasSingleton s s' -> HasSingleton (.proj s K) s'

-- inductive HasSingletonProj : Singleton n k -> Singleton n k -> Kind -> Prop where
--   | here : HasSingleton s s' -> HasSingletonProj (.proj s K) s' K
--   | there : HasSingletonProj s s' K -> HasSingletonProj (.proj s K') s' K

-- theorem HasSingleton.is_not_proj (hh : HasSingleton s (.proj s' K)) : False := by
--   cases hh
--   case proj hh => apply hh.is_not_proj

-- theorem HasSingleton.is_target (hs1 : HasSingleton s t) (hs2 : HasSingleton t u) : t = u := by
--   induction hs1
--   case var => cases hs2; rfl
--   case cvar => cases hs2; rfl
--   case proj ih => apply! ih

-- theorem HasSingletonProj.erase (hs : HasSingletonProj s s' K) : HasSingleton s s' := by
--   induction hs
--   case here => apply! HasSingleton.proj
--   case there ih => apply! HasSingleton.proj

-- inductive ProjectedSingleton: CaptureSet n k -> (CaptureSet n k) -> Prop where
--   | var : ProjectedSingleton {x=x} {x=x}
--   | cvar : ProjectedSingleton {c=c} {c=c}
--   | proj : ProjectedSingleton s C -> ProjectedSingleton s (.proj C K)

-- inductive ProjectedSingletonWith : (CaptureSet n k) -> (K : Kind) -> (CaptureSet n k) -> Prop where
--   | here : ProjectedSingleton s C -> ProjectedSingletonWith s K (.proj C K)
--   | there : ProjectedSingletonWith s K C -> ProjectedSingletonWith s K (.proj C K')

-- def ProjectedSingletonWith.erase (hp : ProjectedSingletonWith s K C) : ProjectedSingleton s C := by
--   induction hp <;> apply! ProjectedSingleton.proj

-- /-- A capture set that only has projections on top of singletons. -/
-- inductive ProjectedSingletonsOnly: CaptureSet n k -> Prop where
--   | empty : ProjectedSingletonsOnly .empty
--   | singleton : ProjectedSingleton s C -> ProjectedSingletonsOnly C
--   | union : ProjectedSingletonsOnly C1 -> ProjectedSingletonsOnly C2 -> ProjectedSingletonsOnly (.union C1 C2)

-- @[simp]
-- def CaptureSet.push_proj (C: CaptureSet n k) (K: Kind) : CaptureSet n k :=
--   match C with
--   | .empty => .empty
--   | .singleton c => proj (.singleton c) K
--   | .csingleton c => proj (.csingleton c) K
--   | .proj C1 K1 => proj (.proj C1 K1) K
--   | .union C1 C2 => .union (C1.push_proj K) (C2.push_proj K)

-- @[simp]
-- def CaptureSet.canonicalize (C : CaptureSet n k) : CaptureSet n k :=
--   match C with
--   | .empty => .empty
--   | .singleton c => .singleton c
--   | .csingleton c => .csingleton c
--   | .union C1 C2 => .union (C1.canonicalize) (C2.canonicalize)
--   | .proj C1 K => C1.canonicalize.push_proj K

-- theorem CaptureSet.push_proj_is_superset (C : CaptureSet n k) : (C.proj K) ⊆ C.push_proj K := by
--   induction C <;> simp only [push_proj]
--   case empty => exists 0; apply Subset.proj_empty
--   case union C1 C2 ih1 ih2 =>
--     apply IsTrans.trans (r := HasSubset.Subset)
--     exists 0; apply Subset.proj_union_r
--     apply! Subset.union_monotone
--   case singleton => exists 0; apply Subset.rfl
--   case csingleton => exists 0; apply Subset.rfl
--   case proj => apply Subset.proj' Subset.rfl'

-- theorem CaptureSet.canonicalize_is_superset {C : CaptureSet n k} : C ⊆ C.canonicalize := by
--   induction C <;> (simp; try apply Subset.rfl')
--   case union ih1 ih2 => apply Subset.union_monotone ih1 ih2
--   case proj C1 K ih =>
--     apply Subset.trans'
--     apply Subset.proj' ih
--     apply push_proj_is_superset

-- theorem CaptureSet.push_proj_is_subset {C : CaptureSet n k} : C.push_proj K ⊆ C.proj K := by
--   induction C <;> (simp; try apply Subset.rfl')
--   case empty => apply Subset.empty'
--   case union C1 C2 ih1 ih2 =>
--     apply Subset.trans' _ Subset.proj_union_l'
--     apply! Subset.union_monotone

-- theorem CaptureSet.canonicalize_is_subset {C : CaptureSet n k} : C.canonicalize ⊆ C := by
--   induction C <;> (simp; try apply Subset.rfl')
--   case union ih1 ih2 => apply Subset.union_monotone ih1 ih2
--   case proj C1 K ih =>
--     apply Subset.trans' C1.canonicalize.push_proj_is_subset
--     apply Subset.proj' ih

-- theorem CaptureSet.push_proj_singleton {C : CaptureSet n k} (hp: ProjectedSingletonsOnly C) : ProjectedSingletonsOnly (C.push_proj K) := by
--   induction hp <;> try simp_all
--   case empty => constructor
--   case singleton hp =>
--     induction hp
--     case var => apply ProjectedSingletonsOnly.singleton (.proj .var)
--     case cvar => apply ProjectedSingletonsOnly.singleton (.proj .cvar)
--     case proj =>
--       apply ProjectedSingletonsOnly.singleton
--       apply ProjectedSingleton.proj
--       apply! ProjectedSingleton.proj
--   case union C1 C2 ih1 ih2 =>
--     apply! ProjectedSingletonsOnly.union

-- theorem CaptureSet.canonicalize_is_projected_singletons_only {C : CaptureSet n k} : ProjectedSingletonsOnly C.canonicalize := by
--   induction C <;> try simp
--   case empty => apply ProjectedSingletonsOnly.empty
--   case singleton => apply ProjectedSingletonsOnly.singleton .var
--   case csingleton => apply ProjectedSingletonsOnly.singleton .cvar
--   case union C1 C2 ih1 ih2 => apply ProjectedSingletonsOnly.union ih1 ih2
--   case proj C K ih =>
--     apply push_proj_singleton
--     assumption

-- lemma CaptureSet.push_proj_depth {C : CaptureSet n k} : (C.push_proj K).depth ≤ 1 + C.depth := by
--   induction C <;> simp; omega

-- theorem CaptureSet.canonicalize_depth {C : CaptureSet n k} : C.canonicalize.depth ≤ C.depth := by
--   induction C <;> simp
--   case union ih1 ih2 => omega
--   case proj C K ih =>
--     apply IsTrans.trans
--     apply C.canonicalize.push_proj_depth
--     simp; exact ih

-- lemma CaptureSet.push_proj_singleton_eq {C : CaptureSet n k} (hp : ProjectedSingleton s C) : (C.push_proj K) = (C.proj K) := by
--   induction hp <;> simp

-- theorem CaptureSet.canonicalize_projected_singletons {C : CaptureSet n k} (hp : ProjectedSingletonsOnly C) : C.canonicalize = C := by
--   induction hp
--   case singleton s C hs =>
--     induction hs <;> simp
--     case proj ha ih =>
--       rw [ih]
--       apply! push_proj_singleton_eq
--   case empty => simp
--   case union ha hb iha ihb =>
--     simp; aesop

-- theorem CaptureSet.canonicalize_idempt {C : CaptureSet n k} : C.canonicalize.canonicalize = C.canonicalize := by
--   have h := C.canonicalize_is_projected_singletons_only
--   rw [C.canonicalize.canonicalize_projected_singletons h]

-- theorem CaptureSet.Subset.canonicalize {A B : CaptureSet n k} (hs : A ⊆ B) : A.canonicalize ⊆ B.canonicalize := by
--   apply trans'
--   apply A.canonicalize_is_subset
--   apply trans' hs
--   apply B.canonicalize_is_superset


-- inductive HasSingleton : CaptureSet n k -> CaptureSet n k -> Prop where
--   | var : HasSingleton {x=x} {x=x}
--   | cvar : HasSingleton {c=c} {c=c}
--   | union_l : HasSingleton s C1 -> HasSingleton s (.union C1 C2)
--   | union_r : HasSingleton s C2 -> HasSingleton s (.union C1 C2)
--   | proj : HasSingleton s C -> HasSingleton (s.proj K) (C.proj K)

-- theorem CaptureSet.Subset.subset_has_singleton' {C1 C2 : CaptureSet n k} (hh1 : HasSingleton s C1) (hs : Subset t C1 C2) : HasSingleton s C2 := by
--   induction hs generalizing s
--   case empty => cases hh1
--   case rfl => assumption
--   case union_l ih1 ih2 =>
--     cases hh1
--     apply! ih1
--     apply! ih2
--   case union_rl ih => apply HasSingleton.union_l; apply ih hh1
--   case union_rr ih => apply HasSingleton.union_r; apply ih hh1
--   case trans ha hb iha ihb =>
--     apply ihb $ iha hh1
--   case proj_empty => cases hh1; rename_i hh1; cases hh1
--   case proj_union_l =>
--     cases hh1
--     { rename_i hh1; cases hh1; constructor; apply! HasSingleton.union_l }
--     { rename_i hh1; cases hh1; constructor; apply! HasSingleton.union_r }
--   case proj_union_r =>
--     cases hh1
--     rename_i hh1
--     cases hh1
--     { apply HasSingleton.union_l; constructor; assumption }
--     { apply HasSingleton.union_r; constructor; assumption }
--   case proj ih =>
--     cases hh1
--     constructor
--     apply! ih

-- theorem CaptureSet.subset_has_singleton {C1 C2 : CaptureSet n k} (hs : C1 ⊆ C2) (hh : HasSingleton C C1) : HasSingleton C C2 := by
--   have ⟨_, h⟩ := hs
--   apply Subset.subset_has_singleton' hh h

-- theorem CaptureSet.projected_singleton_has_singleton (hp : ProjectedSingleton s C) : HasSingleton C C := by
--   induction hp
--   case var => constructor
--   case cvar => constructor
--   case proj hp => constructor; assumption

-- theorem CaptureSet.projected_singleton_unique_singleton (hp : ProjectedSingleton s C) (hh : HasSingleton C' C) : C' = C := by
--   induction hp generalizing C'
--   case var => cases hh; rfl
--   case cvar => cases hh; rfl
--   case proj hp ih =>
--     cases hh
--     rename_i hh
--     have ih1 := ih hh
--     subst_vars
--     simp


-- theorem CaptureSet.Subset.empty_projected_singleton {C : CaptureSet n k} (hs : C ⊆ .empty) (hp : ProjectedSingleton s C) : False := by
--   have ⟨n, h⟩ := hs
--   have h2 := CaptureSet.Subset.subset_has_singleton' (projected_singleton_has_singleton hp) h
--   cases h2

-- end Capless
