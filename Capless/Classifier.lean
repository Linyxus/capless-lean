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
  | union : Disjoint a b1 -> Disjoint a b2 -> Disjoint a (union b1 b2)
  | excl_this : a.subclass b -> Disjoint (excl c b) (classifier a)
  | excl_union : Disjoint a (excl b1 k) -> Disjoint a (excl b2 k) -> Disjoint a (excl (union b1 b2) k)
  | excl : Disjoint a b -> Disjoint a (excl b k)
  | symm : Disjoint a b -> Disjoint b a

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
    apply Disjoint.excl_this
    unfold Classifier.subclass; simp

theorem Kind.subkind_any : Kind.Subkind K .any := by
  induction K
  case classifier a =>
    apply Subkind.base; apply Classifier.subclass_top
  case union a b iha ihb =>
    apply Subkind.union_l <;> assumption
  case excl K c ih =>
    apply Subkind.excl_l ih

/- Classifiers fixed for boundary. -/
def Classifier.control := Classifier.child 0 Classifier.top
def Kind.control := Kind.classifier .control
