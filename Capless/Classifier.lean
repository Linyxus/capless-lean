import Capless.Basic
import Capless.Tactics

namespace Capless

inductive Classifier : Type where
  | top : Classifier
  | child : Nat -> Classifier -> Classifier
deriving DecidableEq

instance : LawfulBEq Classifier where
  rfl := by
    intro a
    induction a <;> simp [BEq.beq]
  eq_of_beq := by
    intro a b h
    induction a <;> induction b <;> simp_all [BEq.beq]

@[simp]
def Classifier.depth (c: Classifier) : Nat :=
  match c with
  | top => 0
  | child _ p => 1 + p.depth

@[simp]
def Classifier.subclass (c1: Classifier) (c2: Classifier) : Bool :=
  if c1 == c2 then true
  else
    match c1 with
    | .top => false
    | .child _ p => p.subclass c2

@[simp]
def Classifier.disjoint (c1: Classifier) (c2: Classifier) : Bool :=
  match c1 with
    | top => false
    | child n p => match c2 with
      | top => false
      | child m q =>
        if p == q then n != m
        else (child n p).disjoint q || p.disjoint (child m q)

inductive Kind : Type where
  | classifier : Classifier -> Kind
  | union : Kind -> Kind -> Kind
  | excl : Kind -> Classifier -> Kind

/-- The top kind -/
def Kind.any := Kind.classifier .top

inductive Kind.Disjoint : Kind -> Kind -> Prop where
  | base : a.disjoint b -> Disjoint (classifier a) (classifier b)
  | union_l : Disjoint a1 b -> Disjoint a2 b -> Disjoint (union a1 a2) b
  | union_r : Disjoint a b1 -> Disjoint a b2 -> Disjoint a (union b1 b2)
  | excl_this_l : a.subclass b -> Disjoint (excl c b) (classifier a)
  | excl_this_r : a.subclass b -> Disjoint (classifier a) (excl c b)
  | excl_union_l : Disjoint (excl a1 k) b -> Disjoint (excl a2 k) b -> Disjoint (excl (union a1 a2) k) b
  | excl_union_r : Disjoint a (excl b1 k) -> Disjoint a (excl b2 k) -> Disjoint a (excl (union b1 b2) k)
  | excl_l : Disjoint a b -> Disjoint (excl a k) b
  | excl_r : Disjoint a b -> Disjoint a (excl b k)
  | empty_l : a.subclass b -> Disjoint (excl (classifier a) b) K
  | empty_r : a.subclass b -> Disjoint K (excl (classifier a) b)

inductive Kind.Subkind : Kind -> Kind -> Prop where
  | base : a.subclass b -> Subkind (classifier a) (classifier b)
  | union_l : Subkind a1 b -> Subkind a2 b -> Subkind (union a1 a2) b
  | union_r1 : Subkind a b1 -> Subkind a (union b1 b2)
  | union_r2 : Subkind a b2 -> Subkind a (union b1 b2)
  | excl_l : Subkind a b -> Subkind (excl a c) b
  | excl_r : Subkind a b -> Kind.Disjoint a (classifier k) -> Subkind a (excl b k)
  | trans : Subkind a b -> Subkind b c -> Subkind a c

theorem Classifier.subclass_top : Classifier.subclass k .top := by
  induction k
  case top => trivial
  case child n p => simp_all

theorem Classifier.subclass_of_top : Classifier.top.subclass k -> k = .top := by
  intro h
  induction k
  case top => trivial
  case child n p ih =>
    simp at h

theorem Classifier.disjoint_symm : Classifier.disjoint a b -> b.disjoint a := by
  intro h
  induction a generalizing b
  case top =>
    simp_all
  case child n p ih =>
    induction b <;> simp at h
    rename_i m q ihb
    simp
    split <;> subst_vars
    simp at h
    false_or_by_contra
    apply h.elim (Eq.symm _)
    assumption
    split at h
    rename_i h0 h1
    apply h0.elim (Eq.symm h1)
    cases h
    { right; apply ihb; assumption }
    { left; apply ih; assumption }

theorem Classifier.neq_child : q ≠ (child n q) := by
  intro h
  induction q
  case top => cases h
  case child m p ih =>
    injections
    apply ih
    subst_vars
    assumption

theorem Classifier.disjoint_top : Classifier.disjoint a .top -> False := by
  intro h
  induction a
  case top => simp at h
  case child n p ih => simp at h

theorem Classifier.subclass_down : subclass a b -> (a = b) ∨ (∃ n, subclass a (.child n b)) := by
  intro h
  induction a generalizing b
  case top => left; symm; apply subclass_of_top; assumption
  case child n p ih =>
    simp at h
    cases h
    case inl h0 => subst_vars; left; trivial
    case inr h0 =>
      right
      cases ih h0
      { subst_vars; exists n; simp; }
      { rename_i h1; have ⟨n, h1⟩ := h1; exists n; simp; right; assumption }

theorem Classifier.subclass_inv : subclass a b -> (a = b) ∨ (∃ n p, a = child n p ∧ p.subclass b) := by
  intro h
  induction a
  case top => left; symm; apply subclass_of_top h
  case child n p ih =>
    simp at h
    cases h
    case inl h => left; assumption
    case inr h =>
      right
      apply Exists.intro n
      apply Exists.intro p
      apply And.intro
      rfl
      cases ih h
      subst_vars
      assumption
      rename_i h
      have ⟨n0, p0, hp, h0⟩ := h
      subst_vars
      assumption


theorem Classifier.subclass_depth : subclass a b -> a.depth >= b.depth := by
  induction a generalizing b
  case top => simp; intro; subst_vars; simp
  case child n p ih =>
    intro h
    simp at h
    cases h
    case inl h => subst_vars; simp
    case inr h => simp; have h0 := ih h; omega

theorem Classifier.subclass_child : subclass a (child n a) -> False := by
  intro h
  have h0 := subclass_depth h
  simp at h0
  omega

theorem Classifier.subclass_up : subclass a (child m b) -> subclass a b := by
  intro h
  induction a generalizing b
  case top => have h0 := subclass_depth h; simp at h
  case child n p ih =>
    simp at h
    cases h
    case inl h =>
      have ⟨hn, h⟩ := h
      subst_vars
      simp
      right
      unfold subclass
      simp
    case inr h =>
      have h0 := ih h
      simp
      right
      assumption

theorem Classifier.subclass_trans : subclass a b -> subclass b c -> subclass a c := by
  intro h1 h2
  induction b
  case top => simp_all
  case child n k ih =>
    have h11 := subclass_up h1
    simp at h2
    cases h2
    case inl h2 => subst_vars; simp_all
    case inr h2 => apply ih h11 h2

theorem Classifier.disjoint_antisymm : disjoint a a = false := by
  induction a <;> simp

theorem Classifier.disjoint_subclass : subclass a b -> disjoint a b = false := by
  intro h
  induction a generalizing b
  case top => simp_all; apply disjoint_antisymm
  case child n p iha =>
    induction b
    case top => simp
    case child m q ihb =>
      simp
      split
      subst_vars
      simp at h
      cases h; assumption; rename_i h; have h0 := subclass_child (a := q) (n := m); contradiction
      apply And.intro
      apply (ihb (subclass_up h))
      cases subclass_inv h
      case inl h => injections; contradiction
      case inr h =>
        have ⟨n0, p0, hp, hh⟩ := h
        injections
        subst_vars
        apply iha
        assumption

theorem Classifier.disjoint_up : disjoint a b -> disjoint a (child m b) := by
  intro h
  induction a generalizing b m
  case top => simp at h
  case child n p ih =>
    induction b generalizing m
    case top => exfalso; apply disjoint_top h
    case child k q ihb =>
      simp at h
      split at h
      subst_vars
      simp
      split
      exfalso; apply neq_child; assumption
      left; assumption
      cases h
      case inl h =>
        have h0 := ihb (m := k) h
        simp
        split
        subst_vars
        { have h1 : (child n (child k q)).subclass (child k q)  := by simp
          have h2 := disjoint_subclass h1
          rw [Bool.eq_false_iff] at h2
          contradiction }
        { left; left; assumption }
      case inr h =>
        simp
        split
        { subst_vars; simp at h }
        { left; right; assumption }

theorem Classifier.subclass_disjoint : subclass a1 a2 -> disjoint b a2 -> disjoint b a1 := by
  intro hs hd
  induction a1
  case top =>
    simp at hs; subst_vars; exfalso; apply disjoint_top hd
  case child n k ih =>
    simp at hs
    cases hs
    case inl h => subst_vars; simp_all
    case inr h => apply disjoint_up; apply ih h

theorem Kind.Disjoint.symm (hd : Disjoint K1 K2) : Disjoint K2 K1 := by
  induction hd
  case base hd =>
    apply base
    apply Classifier.disjoint_symm hd
  case union_l => apply! union_r
  case union_r => apply! union_l
  case excl_this_l => apply! excl_this_r
  case excl_this_r => apply! excl_this_l
  case excl_union_l => apply! excl_union_r
  case excl_union_r => apply! excl_union_l
  case excl_l => apply! excl_r
  case excl_r => apply! excl_l
  case empty_l => apply! empty_r
  case empty_r => apply! empty_l

theorem Kind.Subkind.rfl : Kind.Subkind k k := by
  cases k
  case classifier a =>
    constructor
    unfold Classifier.subclass; simp
  case union a b =>
    apply Subkind.union_l
    apply Subkind.union_r1
    apply rfl
    apply Subkind.union_r2
    apply rfl
  case excl k a =>
    apply Subkind.excl_r
    apply Subkind.excl_l
    apply rfl
    apply Disjoint.excl_this_l
    unfold Classifier.subclass; simp

theorem Kind.subkind_any : Kind.Subkind K .any := by
  induction K
  case classifier a =>
    apply Subkind.base; apply Classifier.subclass_top
  case union a b iha ihb =>
    apply Subkind.union_l <;> assumption
  case excl K c ih =>
    apply Subkind.excl_l ih

theorem Kind.Disjoint.union_r_inv (hd : Disjoint K (.union K1 K2)) : Disjoint K K1 ∧ Disjoint K K2 := by
  cases hd
  case union_l ha hb =>
    have ⟨_, _⟩ := ha.union_r_inv
    have ⟨_, _⟩ := hb.union_r_inv
    apply And.intro <;> apply! union_l
  case union_r ha hb => apply! And.intro
  case excl_union_l ha hb =>
    have ⟨_, _⟩ := ha.union_r_inv
    have ⟨_, _⟩ := hb.union_r_inv
    apply And.intro <;> apply! excl_union_l
  case excl_l ha =>
    have ⟨_, _⟩ := ha.union_r_inv
    apply And.intro <;> apply! excl_l
  case empty_l ha =>
    apply And.intro <;> apply! empty_l


theorem Kind.Disjoint.subclassed_excl_swap (hd : Disjoint K1 (.excl K2 b)) (hsub : b.subclass a) : Disjoint (.excl K1 a) K2 := by
  cases hd
  case union_l ha hb =>
    apply excl_union_l
    apply ha.subclassed_excl_swap hsub
    apply hb.subclassed_excl_swap hsub
  case excl_this_r ha =>
    have h1 := Classifier.subclass_trans ha hsub
    apply empty_l h1
  case excl_union_l ha hb =>



theorem Kind.Disjoint.subclassed_excl (hd : Disjoint (.excl K1 a) (.excl K2 b)) (hsub : b.subclass a) : Disjoint (.excl K1 a) K2 := by
  cases hd
  case excl_union_l ha hb =>
    apply excl_union_l
    apply ha.subclassed_excl hsub
    apply hb.subclassed_excl hsub
  case excl_union_r ha hb =>
    apply union_r
    apply ha.subclassed_excl hsub
    apply hb.subclassed_excl hsub
  case excl_r ha => assumption
  case excl_l ha =>





theorem Kind.Disjoint.disjointed_excl (hd : Disjoint K1 (.excl K2 a)) (hda : Disjoint K1 (.classifier a)) : Disjoint K1 K2 := by
  cases hd
  case union_l ha hb =>
    have ⟨hl, hr⟩ := hda.symm.union_r_inv
    apply union_l (ha.disjointed_excl hl.symm) (hb.disjointed_excl hr.symm)
  case excl_this_r ha =>
    cases hda
    have h := Classifier.disjoint_subclass ha
    simp_all
  case excl_union_l ha hb =>
    cases hda
    case excl_this_l hsub =>
      -- apply excl_union_l

    case excl_l hda =>
      have ⟨hl, hr⟩ := hda.symm.union_r_inv
      apply excl_union_l
      apply ha.disjointed_excl hl.symm.excl_l
      apply hb.disjointed_excl hr.symm.excl_l



theorem Kind.Disjoint.of_subkind (hd : Disjoint K K2) (hs : Subkind K1 K2) : Disjoint K K1 := by
  induction hs generalizing K
  case trans ha hb iha ihb =>
    apply iha $ ihb hd
  case base a b hs =>
    generalize h : Kind.classifier b = K2 at hd
    induction hd <;> try (subst_vars; simp_all)
    case base hd =>
      apply base
      apply! Classifier.subclass_disjoint
    case union_l ha hb => apply! union_l
    case excl_this_l hs1 => apply excl_this_l; apply! Classifier.subclass_trans
    case excl_union_l => apply! excl_union_l
    case excl_l => apply! excl_l
  case union_l ha hb iha ihb =>
    apply union_r
    apply! iha
    apply! ihb
  case union_r1 ha ih =>
    have ⟨_, _⟩ := hd.union_r_inv
    apply! ih
  case union_r2 ha ih =>
    have ⟨_, _⟩ := hd.union_r_inv
    apply! ih
  case excl_l ha ih => apply excl_r; apply! ih
  case excl_r A B k hs ha ih =>
    generalize h : Kind.excl B k = K2 at hd
    induction hd <;> try (subst_vars; simp_all)
    case union_l => apply! union_l
    case excl_this_r hs =>
      have ⟨_, _⟩ := h
      subst_vars; simp_all
      have ha1 := ha.symm
      sorry
    case excl_union_r =>
      have ⟨_, _⟩ := h
      subst_vars; simp_all
      apply ih



    case excl_union_l => apply! excl_union_l
    case excl_l => apply! excl_l


















/- Classifiers fixed for boundary. -/
def Classifier.control := Classifier.child 0 Classifier.top
def Kind.only_control := Kind.classifier .control
