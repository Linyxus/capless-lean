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
  cvars : Finset (Fin k)

inductive CaptureSet.Subset : CaptureSet n k → CaptureSet n k → Prop where
  | mk : ∀ {c1 c2 : CaptureSet n k},
    c1.vars ⊆ c2.vars →
    c1.cvars ⊆ c2.cvars →
    Subset c1 c2

instance CaptureSet.empty : EmptyCollection (CaptureSet n k) where
  emptyCollection := ⟨∅, ∅⟩

instance CaptureSet.union : Union (CaptureSet n k) where
  union c1 c2 :=
    ⟨c1.vars ∪ c2.vars, c1.cvars ∪ c2.cvars⟩

instance : HasSubset (CaptureSet n k) where
  Subset := CaptureSet.Subset

instance CaptureSet.singleton : Singleton (Fin n) (CaptureSet n k) where
  singleton x := ⟨{x}, ∅⟩

def CaptureSet.csingleton (x : Fin k) : CaptureSet n k :=
  ⟨∅, {x}⟩

def CaptureSet.rename (C : CaptureSet n k) (f : FinFun n n') : CaptureSet n' k :=
  ⟨Finset.image f C.vars, C.cvars⟩

def CaptureSet.crename (C : CaptureSet n k) (f : FinFun k k') : CaptureSet n k' :=
  ⟨C.vars, Finset.image f C.cvars⟩

def CaptureSet.weaken (C : CaptureSet n k) : CaptureSet (n+1) k :=
  C.rename FinFun.weaken

def CaptureSet.cweaken (C : CaptureSet n k) : CaptureSet n (k+1) :=
  C.crename FinFun.weaken

def CaptureSet.cweaken1 (C : CaptureSet n (k+1)) : CaptureSet n (k+2) :=
  C.crename FinFun.weaken.ext

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

theorem CaptureSet.cweaken_union {C1 C2 : CaptureSet n k} :
  (C1 ∪ C2).cweaken = C1.cweaken ∪ C2.cweaken := by
  simp [CaptureSet.cweaken, CaptureSet.crename_union]

theorem CaptureSet.rename_singleton {x : Fin n} {f : FinFun n n'} :
  ({x} : CaptureSet n k).rename f = {f x} := by
  simp [CaptureSet.rename, Finset.image_singleton, CaptureSet.singleton]

theorem CaptureSet.rename_csingleton {x : Fin k} {f : FinFun n n'} :
  (CaptureSet.csingleton x).rename f = CaptureSet.csingleton x := by
  simp [CaptureSet.rename, CaptureSet.csingleton]

theorem CaptureSet.crename_singleton {x : Fin n} {f : FinFun k k'} :
  ({x} : CaptureSet n k).crename f = {x} := by
  simp [CaptureSet.crename, CaptureSet.singleton]

theorem CaptureSet.crename_csingleton {x : Fin k} {f : FinFun k k'} :
  (CaptureSet.csingleton x : CaptureSet n k).crename f = CaptureSet.csingleton (f x) := by
  simp [CaptureSet.crename, CaptureSet.csingleton]

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

theorem Finset.weaken_rename {xs : Finset (Fin n)} :
  (xs.image f).image FinFun.weaken = (xs.image FinFun.weaken).image (FinFun.ext f) := by
  simp [Finset.image_image, FinFun.comp_weaken]

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
  C.NonLocal

inductive CaptureSet.CNonLocal : CaptureSet n (k+1) -> Prop where
| mk : ∀ {C : CaptureSet n (k+1)},
  0 ∉ C.cvars ->
  C.CNonLocal

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
  case mk h1 =>
    simp [CaptureSet.rename] at he
    simp at *
    let ⟨he1, he3⟩ := he
    subst he1
    constructor; simp
    apply Finset.nonlocal_rename_l rfl h1

theorem CaptureSet.nonlocal_crename_l
  (he : C0 = C.crename f)
  (h : NonLocal C0) :
  NonLocal C := by
  cases C0; cases C
  cases h
  case mk h1 =>
    simp [CaptureSet.crename] at he
    simp at *
    let ⟨he1, he3⟩ := he
    subst he1
    constructor; simp
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
  case mk h1 =>
    simp at *
    constructor; simp only [CaptureSet.rename]
    apply Finset.nonlocal_rename_r h1

theorem CaptureSet.nonlocal_crename_r
  (h : NonLocal C) :
  NonLocal (C.crename f) := by
  cases C; cases h
  case mk h1 h2 =>
    simp at *
    constructor; simp only [CaptureSet.crename]
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
    rw [Finset.mem_image] at he
    let ⟨a0, he, heq⟩ := he
    simp [pred] at he
    let ⟨a1, he, h⟩ := he
    simp [Fin.ppred] at h
    let ⟨h1, heq1⟩ := h
    subst heq heq1
    simp; trivial
  case mpr =>
    intro he
    rw [<- Finset.forall_mem_not_eq'] at h
    have hne := h _ he
    let a0 := Fin.pred a hne
    have heq : a = Fin.succ a0 := by simp [a0]
    rw [heq]
    apply Finset.mem_image_of_mem
    simp [pred]
    constructor; constructor; exact he
    simp [Fin.ppred]; trivial

theorem Finset.notin_weaken' {xs : Finset (Fin (n+1))}
  (h : 0 ∉ xs) :
  ∃ (xs0 : Finset (Fin n)), xs = xs0.image Fin.succ := by
  exists (Finset.pred xs)
  symm
  apply notin_weaken h

theorem Finset.weaken_notin {xs : Finset (Fin n)} :
  0 ∉ xs.image Fin.succ := by
  intro he
  rw [Finset.mem_image] at he
  let ⟨a0, _, heq⟩ := he
  apply Fin.succ_ne_zero
  trivial

theorem Finset.subset_weaken {xs : Finset (Fin n)}
  (h : ys ⊆ xs.image Fin.succ) :
  ∃ (ys0 : Finset (Fin n)), ys = ys0.image Fin.succ := by
  apply Finset.notin_weaken'
  apply Finset.not_mem_mono
  exact h
  apply Finset.weaken_notin

theorem CaptureSet.subset_weaken {C : CaptureSet n k}
  (h : C0 ⊆ C.weaken) :
  ∃ (C0' : CaptureSet n k), C0 = C0'.weaken := by
  cases h; simp [weaken] at *
  cases C; cases C0; simp [CaptureSet.rename] at *
  rename_i ys3 _ _
  simp [FinFun.weaken] at *
  rename_i h1 _
  apply Finset.subset_weaken at h1
  let ⟨ys1, he1⟩ := h1
  exists ⟨ys1, ys3⟩

theorem CaptureSet.subset_cweaken {C : CaptureSet n k}
  (h : C0 ⊆ C.cweaken) :
  ∃ (C0' : CaptureSet n k), C0 = C0'.cweaken := by
  cases h; simp [cweaken] at *
  cases C; cases C0; simp [CaptureSet.crename] at *
  rename_i ys1 _ _ _
  simp [FinFun.weaken] at *
  rename_i h3
  apply Finset.subset_weaken at h3
  let ⟨ys3, he3⟩ := h3
  exists ⟨ys1, ys3⟩

theorem Finset.weaken_subset_subset {xs ys : Finset (Fin n)}
  (h : xs.image Fin.succ ⊆ ys.image Fin.succ) :
  xs ⊆ ys := by
  intro x hx
  have h : Fin.succ x ∈ ys.image Fin.succ := by
    apply Finset.mem_of_subset
    exact h
    apply Finset.mem_image_of_mem; trivial
  rw [Finset.mem_image] at h
  let ⟨a0, he, heq⟩ := h
  rw [Fin.succ_inj] at heq
  subst heq; trivial

theorem CaptureSet.cweaken_subset_subset {C1 C2 : CaptureSet n k}
  (h : C1.cweaken ⊆ C2.cweaken) :
  C1 ⊆ C2 := by
  cases h; simp [cweaken] at *
  cases C1; cases C2; simp [CaptureSet.crename] at *
  rename_i xs1 xs2 _ _ _ _
  simp [FinFun.weaken] at *
  rename_i h3
  apply Finset.weaken_subset_subset at h3
  constructor <;> aesop

theorem CaptureSet.crename_inj {C1 C2 : CaptureSet n k}
  (hinj : Function.Injective f)
  (h : C1.crename f = C2.crename f) :
  C1 = C2 := by
  cases C1; cases C2
  simp [crename] at *
  simp [Finset.image_inj hinj] at h
  aesop

theorem CaptureSet.rename_inj {C1 C2 : CaptureSet n k}
  (hinj : Function.Injective f)
  (h : C1.rename f = C2.rename f) :
  C1 = C2 := by
  cases C1; cases C2
  simp [rename] at *
  simp [Finset.image_inj hinj] at h
  aesop

theorem CaptureSet.cweaken_inj {C1 C2 : CaptureSet n k}
  (h : C1.cweaken = C2.cweaken) :
  C1 = C2 := by
  simp [cweaken] at h
  apply crename_inj
  apply FinFun.weaken_inj
  aesop

theorem Finset.weaken1_weaken_eq {xs : Finset (Fin (n+1))}
  (h : 0 ∉ xs.image FinFun.weaken.ext) :
  xs.image FinFun.weaken = xs.image FinFun.weaken.ext := by
  rw [Finset.ext_iff]
  intro x
  constructor
  case mp =>
    intro he; simp at *
    have ⟨x0, he1, heq⟩ := he
    exists x0; constructor; trivial
    cases x0 using Fin.cases
    case zero =>
      exfalso; apply h
      exact he1; simp [FinFun.weaken, FinFun.ext]
    case succ y0 =>
      simp [FinFun.ext]; simp [FinFun.weaken] at *; trivial
  case mpr =>
    intro he; simp at *
    have ⟨x0, he1, heq⟩ := he
    exists x0; constructor; trivial
    cases x0 using Fin.cases
    case zero =>
      exfalso; apply h
      exact he1; simp [FinFun.weaken, FinFun.ext]
    case succ y0 =>
      simp [FinFun.ext, FinFun.weaken] at *; trivial

theorem CaptureSet.notin_cweaken1_weaken_eq {C : CaptureSet n (k+1)}
  (h : 0 ∉ C.cweaken1.cvars) :
  C.cweaken1 = C.cweaken := by
  cases C
  case mk xs cs =>
    simp [cweaken, cweaken1, crename] at *
    symm; apply Finset.weaken1_weaken_eq; aesop

theorem CaptureSet.eq_cweaken_notin {C : CaptureSet n (k+1)} {C0 : CaptureSet n k}
  (h : C = C0.cweaken) :
  0 ∉ C.cvars := by
  cases C; cases C0
  simp [cweaken, crename] at *
  have ⟨_, h⟩ := h; subst h
  apply Finset.weaken_notin

theorem CaptureSet.cweaken1_cweaken_eq {C D : CaptureSet n (k+1)}
  (h : D.cweaken = C.cweaken1) :
  C.cweaken1 = C.cweaken := by
  apply notin_cweaken1_weaken_eq
  apply eq_cweaken_notin
  symm; exact h

theorem Finset.weaken_eq_singleton_inv {xs : Finset (Fin n)}
  (h : {x} = xs.image FinFun.weaken) :
  ∃ x0, xs = {x0} ∧ x = x0.succ := by
  rw [Finset.ext_iff] at h
  have hx : x ∈ {x} := by rw [Finset.mem_singleton]
  rw [h] at hx
  rw [Finset.mem_image] at hx
  have ⟨x0, hx0, heq⟩ := hx
  simp [FinFun.weaken] at heq
  exists x0
  constructor
  case left =>
    rw [Finset.ext_iff]
    intro y
    constructor <;> intro hy
    case mp =>
      have h1 := Finset.mem_image_of_mem FinFun.weaken hy
      rw [<- h] at h1
      rw [Finset.mem_singleton] at h1
      simp [FinFun.weaken] at h1
      rw [<- heq] at h1
      rw [Fin.succ_inj] at h1
      rw [Finset.mem_singleton]; trivial
    case mpr =>
      rw [Finset.mem_singleton] at hy
      subst hy; trivial
  case right => symm; trivial

theorem CaptureSet.csingleton_cweaken_eq_inv {C : CaptureSet n k}
  (h : CaptureSet.csingleton c = C.cweaken) :
  ∃ c0, c = c0.succ ∧ C = CaptureSet.csingleton c0 := by
  match C with
  | mk xs cs =>
    simp [csingleton, cweaken, crename] at h
    have ⟨h1, h3⟩ := h
    have ⟨c0, h3, h4⟩ := Finset.weaken_eq_singleton_inv h3
    exists c0; simp [csingleton]; aesop

theorem CaptureSet.cweaken_csingleton {c : Fin k} :
  (CaptureSet.csingleton c : CaptureSet n k).cweaken = CaptureSet.csingleton (c.succ) := by
  simp [csingleton, cweaken, crename, FinFun.weaken]

theorem CaptureSet.rename_id {C : CaptureSet n k} :
  C.rename FinFun.id = C := by
  cases C
  unfold FinFun.id
  simp [CaptureSet.rename]

end Capless
