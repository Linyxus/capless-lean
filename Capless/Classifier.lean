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

def KindFun : Type := Kind -> Kind

@[simp]
def KindFun.excl (f : KindFun) (c : Classifier) := (fun (x: Kind) => x.excl c) ∘ f

@[simp]
def KindFun.prepend (f: KindFun) (c : Classifier) := f ∘ (fun (x: Kind) => x.excl c)

inductive UnderExcl : KindFun -> Prop where
  | empty : UnderExcl id
  | excl : UnderExcl f -> UnderExcl (f.excl c)

theorem UnderExcl.prepend (hu : UnderExcl f) : UnderExcl (f.prepend c) := by
  induction hu
  case empty =>
    simp
    apply excl .empty
  case excl hu ih =>
    simp
    rw [Function.comp_assoc]
    apply excl ih

theorem UnderExcl.one {c : Classifier} : UnderExcl (.excl id c) := .excl .empty

theorem UnderExcl.injective (hu : UnderExcl f) : Function.Injective f := by
  induction hu
  case empty => apply Function.injective_id
  case excl hu ih =>
    intro a b h
    simp at h
    apply ih h

inductive Kind.Disjoint : Nat -> Kind -> Kind -> Prop where
  | base :
    a.disjoint b ->
    Disjoint 0 (classifier a) (classifier b)
  | union_l :
    UnderExcl f ->
    Disjoint n (f a1) b ->
    Disjoint m (f a2) b ->
    Disjoint (1 + n + m) (f $ union a1 a2) b
  | union_r :
    UnderExcl f->
    Disjoint n a (f b1) ->
    Disjoint m a (f b2) ->
    Disjoint (1 + n + m) a (f $ union b1 b2)
  | excl_this_l :
    a.subclass b ->
    Disjoint 0 (excl c b) (classifier a)
  | excl_this_r :
    a.subclass b ->
    Disjoint 0 (classifier a) (excl c b)
  | excl_l :
    UnderExcl f ->
    Disjoint n a b ->
    Disjoint (1 + n) (f a) b
  | excl_r :
    UnderExcl f ->
    Disjoint n a b ->
    Disjoint (1 + n) a (f b)
  | excl_up_l :
    UnderExcl f ->
    Disjoint n (f $ .excl k1 a) k2 ->
    Disjoint (1 + n) (.excl (f k1) a) k2
  | excl_up_r :
    UnderExcl f ->
    Disjoint n k1 (f $ .excl k2 a) ->
    Disjoint (1 + n) k1 (.excl (f k2) a)
  | empty_l :
    UnderExcl f ->
    a.subclass b ->
    Disjoint 0 (excl (f $ classifier a) b) K
  | empty_r :
    UnderExcl f ->
    a.subclass b ->
    Disjoint 0 K (excl (f $ classifier a) b)

inductive Kind.Subkind : Kind -> Kind -> Prop where
  | base : a.subclass b -> Subkind (classifier a) (classifier b)
  | union_l : Subkind a1 b -> Subkind a2 b -> Subkind (union a1 a2) b
  | union_r1 : Subkind a b1 -> Subkind a (union b1 b2)
  | union_r2 : Subkind a b2 -> Subkind a (union b1 b2)
  | excl_l : Subkind a b -> Subkind (excl a c) b
  | excl_r : Subkind a b -> Kind.Disjoint n a (classifier k) -> Subkind a (excl b k)
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

theorem Kind.Disjoint.symm (hd : Disjoint n K1 K2) : Disjoint n K2 K1 := by
  induction hd
  case base hd =>
    have hd1 := Classifier.disjoint_symm hd
    apply! base
  case union_l => apply! union_r
  case union_r => apply! union_l
  case excl_this_l => apply! excl_this_r
  case excl_this_r => apply! excl_this_l
  -- case excl_union_l => apply! excl_union_r
  -- case excl_union_r => apply! excl_union_l
  case excl_l => apply! excl_r
  case excl_r => apply! excl_l
  case excl_up_l => apply! excl_up_r
  case excl_up_r => apply! excl_up_l
  case empty_l => apply! empty_r
  case empty_r => apply! empty_l

theorem Kind.Disjoint.union_r_inv (hd : Disjoint n K (.union K1 K2)) : ∃ n1 n2 : Nat, n1 ≤ n ∧ n2 ≤ n ∧ Disjoint n1 K K1 ∧ Disjoint n2 K K2 := by
  generalize h : Kind.union K1 K2 = K at hd
  cases hd <;> (subst_vars; try contradiction; try simp at hd)
  case union_l hu ha hb =>
    have ⟨na1, na2, ⟨_, _, _, _⟩⟩ := ha.union_r_inv
    have ⟨nb1, nb2, ⟨_, _, _, _⟩⟩ := hb.union_r_inv
    exists 1 + na1 + nb1, 1 + na2 + nb2
    apply And.intro; omega
    apply And.intro; omega
    apply And.intro <;> apply! union_l
  case union_r hu ha hb =>
    cases hu <;> try cases h
    rename_i n m
    exists n, m
    apply And.intro; omega
    apply And.intro; omega
    apply! And.intro
  case excl_l hu ha =>
    have ⟨na1, na2, ⟨_, _, _, _⟩⟩ := ha.union_r_inv
    exists 1 + na1, 1 + na2
    apply And.intro; omega
    apply And.intro; omega
    apply And.intro <;> apply! excl_l
  case excl_r hu ha =>
    cases hu <;> try cases h
    have ⟨na1, na2, ⟨_, _, _, _⟩⟩ := ha.union_r_inv
    exists na1, na2
    apply And.intro; omega
    apply And.intro; omega
    apply! And.intro
  case excl_up_l ha =>
    have ⟨na1, na2, ⟨_, _, _, _⟩⟩ := ha.union_r_inv
    exists 1 + na1, 1 + na2
    apply And.intro; omega
    apply And.intro; omega
    apply And.intro <;> apply! excl_up_l
  case empty_l ha =>
    exists 0, 0
    apply And.intro; omega
    apply And.intro; omega
    apply And.intro <;> apply! empty_l

theorem UnderExcl.excl_fold {f : KindFun} (hu : UnderExcl f) : (f.excl c) k = (f k).excl c := by
  induction hu <;> simp_all

theorem UnderExcl.compose (hu1 : UnderExcl f) (hu2 : UnderExcl g) : UnderExcl (f ∘ g) := by
  induction hu1
  case empty =>
    rw [Function.id_comp]
    assumption
  case excl hu ih =>
    rw [KindFun.excl]
    rw [Function.comp_assoc]
    rw [← KindFun.excl]
    constructor; assumption

theorem UnderExcl.prefix (hf : UnderExcl f) (hg : UnderExcl g) (he : f k1 = g k2) : (∃ h, UnderExcl h ∧ f = g ∘ h) ∨ (∃ h, UnderExcl h ∧ g = f ∘ h) := by
  induction hf generalizing g k1 k2
  case empty =>
    right
    exists g
  case excl f' c hf ih =>
    simp at he
    cases hg
    case empty => simp at he; subst_vars; simp_all; left; apply! excl
    case excl g' c' hg =>
      simp at he; have ⟨_, _⟩ := he; subst_vars; simp_all
      cases ih hg he
      case inl ih =>
        have ⟨h, hh1, hh2⟩ := ih
        left
        exists h
        apply And.intro; assumption
        rw [Function.comp_assoc, hh2]
      case inr ih =>
        have ⟨h, hh1, hh2⟩ := ih
        right
        exists h
        apply And.intro; assumption
        rw [Function.comp_assoc, hh2]

theorem UnderExcl.union_eq (hf : UnderExcl f) (hg : UnderExcl g) (he : g k = f (.union k1 k2)) : ∃ h, UnderExcl h ∧ f = g ∘ h := by
  induction hg generalizing f k k1 k2
  case empty =>
    exists f
  case excl g' c hg ih =>
    simp at he
    cases hf
    case empty => cases he
    case excl f' c' hf =>
      simp at he; have ⟨_, _⟩ := he; subst_vars
      rename_i hf'
      unfold KindFun.excl
      have ⟨h, ⟨_, hh⟩⟩ := ih hf hf'
      exists h
      apply And.intro; assumption
      rw [Function.comp_assoc]
      rw [hh]
  -- case empty =>
  --   induction hg
  --   case empty => simp_all; apply empty
  --   case excl hg ih => simp_all
  -- case excl f c hf ihf =>

    -- induction hg generalizing f c k k1 k2
    -- case empty => simp_all; constructor; apply hf
    -- case excl hg ihg =>
    --   simp at he; have ⟨_, _⟩ := he; subst_vars

theorem Kind.Disjoint.excl_up_r_inv (hd : Disjoint n a (.excl (f b) c)) (hf : UnderExcl f) : ∃ m, Disjoint m a (f (.excl b c)) := by sorry
  -- generalize he : (f b).excl c = K at hd
  -- cases hd <;> (subst_vars; try simp_all)
  -- case union_l hu ha hb =>
  --   -- have ⟨ma, _, _⟩ := ha.excl_up_r_inv hf
  --   -- have ⟨mb, _, _⟩ := hb.excl_up_r_inv hf
  --   exists 1 + ma + mb
  --   apply And.intro; omega
  --   apply! union_l
  -- case union_r hu ha hb =>
  --   have ⟨h, hh1, _⟩ := UnderExcl.union_eq hu hf.excl he
  --   subst_vars
  --   have he1 := hf.excl.injective he
  --   subst_vars





theorem Kind.Disjoint.subclassed_excl_swap (hd : Disjoint n (g (.excl K1 b)) K2) (hg : UnderExcl g) (hsub : b.subclass a) : ∃ m, Disjoint m (g K1) (.excl K2 a) := by
  generalize he : g (Kind.excl K1 b) = K at hd
  cases hd <;> (subst_vars; try contradiction; try simp at hd)
  case base hd =>
    cases hg <;> cases he
  case union_l hu ha hb =>
    -- have hq : g (K1.excl b) = (g.excl b) K1 := by simp
    have ⟨h, hh1, hh2⟩ := UnderExcl.union_eq hu hg.prepend he
    subst_vars; simp_all
    have ⟨ma, ha⟩ := ha.subclassed_excl_swap hg hsub
    have ⟨mb, hb⟩ := hb.subclassed_excl_swap hg hsub
    have he1 := hg.injective he
    injections; subst K1
    exists 1 + ma + mb
    apply union_l (hg.compose hh1) ha hb
  case union_r f _ _ _ _ hu ha hb =>
    have ⟨ma, _⟩ := ha.subclassed_excl_swap hg hsub
    have ⟨mb, _⟩ := hb.subclassed_excl_swap hg hsub
    exists 1 + ma + mb
    rw [← hu.excl_fold] at *
    apply! union_r hu.excl
  case excl_this_l ha =>
    cases hg <;> (simp at he; have ⟨_, _⟩ := he; subst_vars; simp_all)
    case empty =>
      exists 0
      apply empty_r .empty
      apply! Classifier.subclass_trans
    case excl g _ hg =>
      exists 1 + 0
      apply excl_r .one
      apply! excl_this_l
  -- case excl_union_l ha hb =>
  --   have ⟨ma, _⟩ := ha.subclassed_excl_swap hsub
  --   have ⟨mb, _⟩ := hb.subclassed_excl_swap hsub
  --   exists 1 + ma + mb
  --   apply! union_l
  -- case excl_union_r ha hb =>
  --   have ⟨ma, _⟩ := ha.subclassed_excl_swap hsub
  --   have ⟨mb, _⟩ := hb.subclassed_excl_swap hsub
  case excl_l f n a hu ha =>
    cases hg.prefix hu he
    case inl ih =>
      have ⟨h, hh1, hh2⟩ := ih
      subst_vars; simp_all
      have he1 := hu.injective he
      subst_vars
      have ⟨ma, _⟩ := ha.subclassed_excl_swap hh1 hsub
      exists 1 + ma
      apply! excl_l
    case inr ih =>
      have ⟨h, hh1, hh2⟩ := ih
      subst_vars; simp_all
      have he1 := hg.injective he
      cases hh1
      case empty =>
        simp at he1; subst_vars; simp_all
        have ⟨ma, ha1⟩ := ha.subclassed_excl_swap .empty hsub
        exists 1 + ma
        apply! excl_l
      case excl h' c hh1 =>
        simp at he1; have ⟨_, _⟩ := he1; subst_vars; simp_all
        exists 1 + (1 + n)
        apply excl_r .one
        apply excl_l (hg.compose hh1) ha
    -- induction hu
    -- case empty =>
    --   subst_vars
    --   apply! ha.subclassed_excl_swap
    -- case excl hu ih =>
    --   simp at he;
    --   cases hg <;> (simp at he; have ⟨_, _⟩ := he; subst_vars; simp_all)
    --   case empty =>
    --     exists 1 + (1 + n)
    --     apply excl_r .one
    --     apply! excl_l
    --   case excl hg =>

      -- have ⟨_, _⟩ := he; subst_vars; simp_all
      -- rename_i n _ _ _
      -- exists 1 + (1 + n)
      -- apply excl_r UnderExcl.empty.excl
      -- apply excl_l hu ha
  -- case excl_r c1 hu ha =>
  --   have ⟨ma, ha1⟩ := ha.subclassed_excl_swap hsub
  --   rw [← hu.excl_fold]
  --   simp
  --   exists 1 + (1 + ma)
  --   apply excl_up_r hu
  --   apply! excl_r
  case excl_up_l hu ha =>
    simp at h; have ⟨_, _⟩ := h; subst_vars; simp_all

    -- have
    -- induction hu
    -- case empty =>
    --   simp_all; have ⟨_, _⟩ := h; subst_vars; simp_all
    --   apply ha.subclassed_excl_swap hsub
    -- case excl hu _ =>
    --   simp_all; have ⟨_, _⟩ := h; subst_vars; simp_all
      -- have ⟨ma, _⟩ := ha.subclassed_excl_swap hsub


    -- have ⟨ma, ha1⟩ := ha.subclassed_excl_swap hsub









  -- case excl_this ha =>
  --   exists 1 + 0
  --   apply symm
  --   apply empty
  --   apply Classifier.subclass_trans ha hsub
  -- case excl_union na a nb b ha hb =>
  --   have ⟨ma, _⟩ := ha.subclassed_excl_swap hsub
  --   have ⟨mb, _⟩ := hb.subclassed_excl_swap hsub
  --   exists 1 + ma + mb
  --   apply! union
  -- case

-- theorem Kind.Disjoint.subclassed_excl (hd : Disjoint (.excl K1 a) (.excl K2 b)) (hsub : b.subclass a) : Disjoint (.excl K1 a) K2 := by
--   cases hd
--   case excl_union_l ha hb =>
--     apply excl_union_l
--     apply ha.subclassed_excl hsub
--     apply hb.subclassed_excl hsub
--   case excl_union_r ha hb =>
--     apply union_r
--     apply ha.subclassed_excl hsub
--     apply hb.subclassed_excl hsub
--   case excl_r ha => assumption
--   case excl_l ha =>





-- theorem Kind.Disjoint.disjointed_excl (hd : Disjoint K1 (.excl K2 a)) (hda : Disjoint K1 (.classifier a)) : Disjoint K1 K2 := by
--   cases hd
--   case union_l ha hb =>
--     have ⟨hl, hr⟩ := hda.symm.union_r_inv
--     apply union_l (ha.disjointed_excl hl.symm) (hb.disjointed_excl hr.symm)
--   case excl_this_r ha =>
--     cases hda
--     have h := Classifier.disjoint_subclass ha
--     simp_all
--   case excl_union_l ha hb =>
--     cases hda
--     case excl_this_l hsub =>
--       -- apply excl_union_l

--     case excl_l hda =>
--       have ⟨hl, hr⟩ := hda.symm.union_r_inv
--       apply excl_union_l
--       apply ha.disjointed_excl hl.symm.excl_l
--       apply hb.disjointed_excl hr.symm.excl_l



-- theorem Kind.Disjoint.of_subkind (hd : Disjoint n K K2) (hs : Subkind K1 K2) : ∃ m, Disjoint m K K1 := by
--   induction hs generalizing K n
--   case trans ha hb iha ihb =>
--     have ⟨m, hb⟩ := ihb hd
--     apply! iha (n:=m)
--   case base a b hs =>
--     generalize h : Kind.classifier b = K2 at hd
--     induction hd <;> try (subst_vars; simp_all)
--     case base hd =>
--       exists 0
--       apply base
--       apply! Classifier.subclass_disjoint
--     case union_l ha hb =>
--       have ⟨n, _⟩ := ha
--       have ⟨m, _⟩ := hb
--       exists 1 + n + m
--       apply! union_l
--     case excl_this_l hs1 =>
--       exists 0
--       apply excl_this_l; apply! Classifier.subclass_trans
--     case excl_l ha =>
--       have ⟨n, _⟩ := ha
--       exists 1 + n
--       apply! excl_l
--     case union_r hu _ _ ha hb => cases hu <;> cases h
--     case excl_r n _ _ hu ha ih =>
--       cases hu <;> cases h
--       exists n

--   case union_l ha hb iha ihb =>
--     apply union_r
--     apply! iha
--     apply! ihb
--   case union_r1 ha ih =>
--     have ⟨_, _⟩ := hd.union_r_inv
--     apply! ih
--   case union_r2 ha ih =>
--     have ⟨_, _⟩ := hd.union_r_inv
--     apply! ih
--   case excl_l ha ih => apply excl_r; apply! ih
--   case excl_r A B k hs ha ih =>
--     generalize h : Kind.excl B k = K2 at hd
--     induction hd <;> try (subst_vars; simp_all)
--     case union_l => apply! union_l
--     case excl_this_r hs =>
--       have ⟨_, _⟩ := h
--       subst_vars; simp_all
--       have ha1 := ha.symm
--       sorry
--     case excl_union_r =>
--       have ⟨_, _⟩ := h
--       subst_vars; simp_all
--       apply ih



  --   case excl_union_l => apply! excl_union_l
  --   case excl_l => apply! excl_l


















/- Classifiers fixed for boundary. -/
def Classifier.control := Classifier.child 0 Classifier.top
def Kind.only_control := Kind.classifier .control
