import Capless.Basic
import Capless.Tactics

namespace Capless

inductive Classifier : Type where
  | top : Classifier
  | child : Nat -> Classifier -> Classifier
deriving DecidableEq

inductive Classifier.Subclass : Classifier -> Classifier -> Prop where
  | eq : Subclass a a
  | parent_l : Subclass a b -> Subclass (child n a) b

inductive Classifier.Disjoint : Classifier -> Classifier -> Prop where
  | base : n != m -> Disjoint (child n p) (child m p)
  | left : Disjoint a b -> Disjoint (child n a) b
  | right : Disjoint a b -> Disjoint a (child m b)

theorem Classifier.Subclass.of_top : Subclass a .top := by
  induction a
  case top => apply eq
  case child n k ih => apply parent_l ih

theorem Classifier.Subclass.parent_r (hs : Subclass a (child n b)) : Subclass a b := by
  cases hs
  case eq => apply parent_l .eq
  case parent_l hp =>
    apply parent_l hp.parent_r

theorem Classifier.Subclass.trans (h1 : Subclass a b) (h2 : Subclass b c) : Subclass a c := by
  induction h2
  case eq => assumption
  case parent_l hp ih => apply ih h1.parent_r

theorem Classifier.Subclass.down_r (hs : Subclass a b) : a = b ∨ ∃ n, Subclass a (child n b) := by
  induction hs
  case eq => simp
  case parent_l ih =>
    rename_i n _
    right
    cases ih
    case inl ih => subst_vars; exists n; constructor
    case inr ih =>
      have ⟨m, ih⟩ := ih
      exists m
      apply parent_l ih

theorem Classifier.Disjoint.symm (hd : Disjoint a b) : Disjoint b a := by
  induction hd
  case base hne =>
    apply base; aesop
  case left => apply! right
  case right => apply! left

theorem Classifier.Disjoint.refines_subclass_r
  (hd : Disjoint b a2)
  (hs : Subclass a1 a2) : Disjoint b a1 := by
  induction hs
  case eq => assumption
  case parent_l hs ih =>
    apply right $ ih hd

theorem Classifier.subclass_or_disjoint :
  Subclass a b ∨ Subclass b a ∨ Disjoint a b := by
  induction a
  case top => right; left; apply Subclass.of_top
  case child n k ih =>
    cases ih
    case inl ih =>
      left; constructor; assumption
    case inr ih =>
      cases ih
      case inl ih =>
        cases ih.down_r
        { subst_vars; left; apply Subclass.parent_l .eq }
        { rename_i ih1; have ⟨m, ih1⟩ := ih1;
          generalize h : (n == m) = h0;
          cases h0
          right; right;
          apply Disjoint.refines_subclass_r; apply Disjoint.base (m:=m); aesop; assumption
          have h0 := LawfulBEq.eq_of_beq h; subst_vars; right; left; assumption
        }
      case inr ih =>
        right; right; apply Disjoint.left ih


-- instance : LawfulBEq Classifier where
--   rfl := by
--     intro a
--     induction a <;> simp [BEq.beq]
--   eq_of_beq := by
--     intro a b h
--     induction a <;> induction b <;> simp_all [BEq.beq]

-- @[simp]
-- def Classifier.depth (c: Classifier) : Nat :=
--   match c with
--   | top => 0
--   | child _ p => 1 + p.depth

-- @[simp]
-- def Classifier.subclass (c1: Classifier) (c2: Classifier) : Bool :=
--   if c1 == c2 then true
--   else
--     match c1 with
--     | .top => false
--     | .child _ p => p.subclass c2

-- @[simp]
-- def Classifier.disjoint (c1: Classifier) (c2: Classifier) : Bool :=
--   match c1 with
--     | top => false
--     | child n p => match c2 with
--       | top => false
--       | child m q =>
--         if p == q then n != m
--         else (child n p).disjoint q || p.disjoint (child m q)

-- inductive Kind : Type where
--   -- a tree dropping some classifiers
--   | empty
--   | singleton : Classifier -> List Classifier -> Kind
--   | union : Kind -> Kind -> Kind

-- /-- The top kind -/
-- def Kind.any := singleton .top []

-- theorem Classifier.subclass_rfl : Classifier.subclass k k := by
--   unfold Classifier.subclass
--   simp


-- theorem Classifier.subclass_top : Classifier.subclass k .top := by
--   induction k
--   case top => trivial
--   case child n p => simp_all

-- theorem Classifier.subclass_of_top : Classifier.top.subclass k -> k = .top := by
--   intro h
--   induction k
--   case top => trivial
--   case child n p ih =>
--     simp at h

-- theorem Classifier.disjoint_symm : Classifier.disjoint a b -> b.disjoint a := by
--   intro h
--   induction a generalizing b
--   case top =>
--     simp_all
--   case child n p ih =>
--     induction b <;> simp at h
--     rename_i m q ihb
--     simp
--     split <;> subst_vars
--     simp at h
--     false_or_by_contra
--     apply h.elim (Eq.symm _)
--     assumption
--     split at h
--     rename_i h0 h1
--     apply h0.elim (Eq.symm h1)
--     cases h
--     { right; apply ihb; assumption }
--     { left; apply ih; assumption }

-- theorem Classifier.neq_child : q ≠ (child n q) := by
--   intro h
--   induction q
--   case top => cases h
--   case child m p ih =>
--     injections
--     apply ih
--     subst_vars
--     assumption

-- theorem Classifier.disjoint_top : Classifier.disjoint a .top -> False := by
--   intro h
--   induction a
--   case top => simp at h
--   case child n p ih => simp at h

-- theorem Classifier.subclass_down : subclass a b -> (a = b) ∨ (∃ n, subclass a (.child n b)) := by
--   intro h
--   induction a generalizing b
--   case top => left; symm; apply subclass_of_top; assumption
--   case child n p ih =>
--     simp at h
--     cases h
--     case inl h0 => subst_vars; left; trivial
--     case inr h0 =>
--       right
--       cases ih h0
--       { subst_vars; exists n; simp; }
--       { rename_i h1; have ⟨n, h1⟩ := h1; exists n; simp; right; assumption }

-- theorem Classifier.subclass_inv : subclass a b -> (a = b) ∨ (∃ n p, a = child n p ∧ p.subclass b) := by
--   intro h
--   induction a
--   case top => left; symm; apply subclass_of_top h
--   case child n p ih =>
--     simp at h
--     cases h
--     case inl h => left; assumption
--     case inr h =>
--       right
--       apply Exists.intro n
--       apply Exists.intro p
--       apply And.intro
--       rfl
--       cases ih h
--       subst_vars
--       assumption
--       rename_i h
--       have ⟨n0, p0, hp, h0⟩ := h
--       subst_vars
--       assumption


-- theorem Classifier.subclass_depth : subclass a b -> a.depth >= b.depth := by
--   induction a generalizing b
--   case top => simp; intro; subst_vars; simp
--   case child n p ih =>
--     intro h
--     simp at h
--     cases h
--     case inl h => subst_vars; simp
--     case inr h => simp; have h0 := ih h; omega

-- theorem Classifier.subclass_child : subclass a (child n a) -> False := by
--   intro h
--   have h0 := subclass_depth h
--   simp at h0
--   omega

-- theorem Classifier.subclass_up : subclass a (child m b) -> subclass a b := by
--   intro h
--   induction a generalizing b
--   case top => have h0 := subclass_depth h; simp at h
--   case child n p ih =>
--     simp at h
--     cases h
--     case inl h =>
--       have ⟨hn, h⟩ := h
--       subst_vars
--       simp
--       right
--       unfold subclass
--       simp
--     case inr h =>
--       have h0 := ih h
--       simp
--       right
--       assumption

-- theorem Classifier.subclass_trans : subclass a b -> subclass b c -> subclass a c := by
--   intro h1 h2
--   induction b
--   case top => simp_all
--   case child n k ih =>
--     have h11 := subclass_up h1
--     simp at h2
--     cases h2
--     case inl h2 => subst_vars; simp_all
--     case inr h2 => apply ih h11 h2

-- theorem Classifier.disjoint_antisymm : disjoint a a = false := by
--   induction a <;> simp

-- theorem Classifier.disjoint_subclass : subclass a b -> disjoint a b = false := by
--   intro h
--   induction a generalizing b
--   case top => simp_all; apply disjoint_antisymm
--   case child n p iha =>
--     induction b
--     case top => simp
--     case child m q ihb =>
--       simp
--       split
--       subst_vars
--       simp at h
--       cases h; assumption; rename_i h; have h0 := subclass_child (a := q) (n := m); contradiction
--       apply And.intro
--       apply (ihb (subclass_up h))
--       cases subclass_inv h
--       case inl h => injections; contradiction
--       case inr h =>
--         have ⟨n0, p0, hp, hh⟩ := h
--         injections
--         subst_vars
--         apply iha
--         assumption

-- theorem Classifier.disjoint_up : disjoint a b -> disjoint a (child m b) := by
--   intro h
--   induction a generalizing b m
--   case top => simp at h
--   case child n p ih =>
--     induction b generalizing m
--     case top => exfalso; apply disjoint_top h
--     case child k q ihb =>
--       simp at h
--       split at h
--       subst_vars
--       simp
--       split
--       exfalso; apply neq_child; assumption
--       left; assumption
--       cases h
--       case inl h =>
--         have h0 := ihb (m := k) h
--         simp
--         split
--         subst_vars
--         { have h1 : (child n (child k q)).subclass (child k q)  := by simp
--           have h2 := disjoint_subclass h1
--           rw [Bool.eq_false_iff] at h2
--           contradiction }
--         { left; left; assumption }
--       case inr h =>
--         simp
--         split
--         { subst_vars; simp at h }
--         { left; right; assumption }

-- theorem Classifier.subclass_disjoint : subclass a1 a2 -> disjoint b a2 -> disjoint b a1 := by
--   intro hs hd
--   induction a1
--   case top =>
--     simp at hs; subst_vars; exfalso; apply disjoint_top hd
--   case child n k ih =>
--     simp at hs
--     cases hs
--     case inl h => subst_vars; simp_all
--     case inr h => apply disjoint_up; apply ih h

-- theorem Classifier.subclass_child_inj : subclass (child n p) (child m p) -> n = m := by
--   intro h
--   unfold subclass at h
--   split at h
--   case isTrue h0 => have h1 := LawfulBEq.eq_of_beq h0; injections
--   case isFalse =>
--     simp at h
--     have h0 := subclass_depth h
--     simp at h0
--     omega

-- theorem Classifier.disjoint_or_subclass : subclass a b ∨ subclass b a ∨ disjoint a b := by
--   induction a
--   case top => right; left; apply subclass_top
--   case child n p ih =>
--     cases ih
--     case inl ih =>
--       left
--       unfold subclass; simp; right; assumption
--     case inr ih =>
--       cases ih
--       case inl ih =>
--         cases subclass_down ih
--         case inl =>
--           subst_vars
--           left
--           unfold subclass; simp; right; assumption
--         case inr ih =>
--           have ⟨m, ih⟩ := ih
--           generalize h : (m == n) = h0
--           cases h0
--           case false =>
--             right; right;
--             unfold disjoint; simp
--             split
--             rename_i h0 _;
--             cases Classifier.subclass_of_top ih
--             split
--             subst_vars
--             have ih0 := subclass_child_inj ih
--             subst_vars
--             simp
--             aesop










inductive Kind : Type where
| empty : Kind
| singleton : Classifier -> List Classifier -> Kind
| union : Kind -> Kind -> Kind

inductive HasSuperclassOf : Classifier -> List Classifier -> Prop where
  | here : b.Subclass a -> HasSuperclassOf b (a :: xs)
  | there : HasSuperclassOf b xs -> HasSuperclassOf b (a :: xs)

inductive IsEmpty : Kind -> Prop where
  | empty : IsEmpty .empty
  | absurd : HasSuperclassOf a es -> IsEmpty (.singleton a es)
  | union : IsEmpty K1 -> IsEmpty K2 -> IsEmpty (.union K1 K2)

inductive Kind.Disjoint : Kind -> Kind -> Prop where
  | empty_l : Disjoint .empty K
  | empty_r : Disjoint K .empty
  -- empty classifiers are disjoint with everything else
  | absurd_l : HasSuperclassOf a es -> Disjoint (singleton a es) K2
  | absurd_r : HasSuperclassOf a es -> Disjoint K1 (singleton a es)
  -- Otherwise, the root has to be a subclass of the other's exclude list
  | root_l : HasSuperclassOf r1 es2 -> Disjoint (singleton r1 es1) (singleton r2 es2)
  | root_r : HasSuperclassOf r2 es1 -> Disjoint (singleton r1 es1) (singleton r2 es2)
  -- union case
  | union_l : Disjoint K1 K -> Disjoint K2 K -> Disjoint (K1.union K2) K
  | union_r : Disjoint K K1 -> Disjoint K K2 -> Disjoint K (K1.union K2)

-- Note that RHS is always singleton
inductive Kind.Subtract : Nat -> Kind -> Kind -> Kind -> Prop where
  -- empty singletons are subkinds of everything
  | absurd_l : HasSuperclassOf a es ->
    Subtract 0 (singleton a es) K .empty
  | absurd_r : HasSuperclassOf a es ->
    Subtract 0 K (singleton a es) .empty
  | empty_l : Subtract 0 .empty K .empty
  | empty_r : Subtract 0 K .empty K
  -- if excl is empty on RHS, LHS must be a subclass
  | subclass_empty : r1.Subclass r2 ->
    Subtract 0 (singleton r1 es1) (singleton r2 []) .empty
  -- if excl is non-empty on RHS, it must _only_ contain either irrelevant nodes, or subclasses of the LHS's excl list
  | excl_subclass_r :
    a.Subclass r2 -> -- not absurd
    HasSuperclassOf a es1 ->
    Subtract n (singleton r1 es1) (singleton r2 es2) R ->
    Subtract (1 + n) (singleton r1 es1) (singleton r2 (a :: es2)) R
  | excl_disjoint_r :
    a.Subclass r2 -> -- not absurd
    r1.Disjoint a ->
    Subtract n (singleton r1 es1) (singleton r2 es2) R ->
    Subtract (1 + n) (singleton r1 es1) (singleton r2 (a :: es2)) R
  -- otherwise, we have to add a residue
  | disjoint :
    r1.Disjoint r2 ->
    Subtract 0 (singleton r1 es1) (singleton r2 []) (singleton r1 es1)
  | subclass :
    r2.Subclass r1 ->
    Subtract 0 (singleton r1 es1) (singleton r2 []) (singleton r1 (r2 :: es1))
  | residue :
    a.Subclass r2 ->
    a.Subclass r1 ->
    Subtract n (singleton r1 es1) (singleton r2 es2) R ->
    Subtract (1 + n) (singleton r1 es1) (singleton r2 (a :: es2)) (.union R (singleton a es1))
  | union_l :
    Subtract n K1 K R1 ->
    Subtract m K2 K R2 ->
    Subtract (1 + max n m) (.union K1 K2) K (.union R1 R2)
  | union_rl :
    Subtract n K K1 R1 ->
    Subtract m R1 K2 R2 ->
    Subtract (1 + max n m) K (union K1 K2) R2
  | union_rr :
    Subtract n K K2 R2 ->
    Subtract m R2 K1 R1 ->
    Subtract (1 + max n m) K (union K1 K2) R1

inductive Kind.Subkind : Kind -> Kind -> Prop where
  | subtract : Subtract n K1 K2 R -> IsEmpty R -> Subkind K1 K2

-- theorem Kind.Subtract.singleton_empty_subclass
--   (hs : Subtract n (singleton r1 es1) (singleton r2 es2) .empty) :
--     HasSuperclassOf r1 es1

-- theorem Kind.Subtract.empty_excl_append_singleton
--   (hs : Subtract n (singleton r1 es1) (singleton r2 es2) .empty)
--   : ∃ m, Subtract m (singleton r1 (a :: es1)) (singleton r2 es2) .empty := by
--   cases hs
--   case absurd_l hs =>
--     exists 0
--     apply excl_empty $ .there hs
--   case subclass_l =>
--     exists 0
--     apply! subclass_l
--   case excl_subclass_r hs ha ih =>
--     have ⟨m, _⟩ := ih.empty_excl_append_singleton (a:=a)
--     exists 1 + m
--     apply! excl_subclass_r ha (.there hs)
--   case excl_disjoint_r hd ih =>
--     have ⟨m, _⟩ := ih.empty_excl_append_singleton (a:=a)
--     exists 1 + m
--     apply! excl_disjoint_r hd

theorem Kind.Subtract.rfl_singleton :
  ∃ m, Subtract m (singleton r es) (singleton r es) .empty := by
  induction es
  case nil =>
    exists 0
    apply subclass_l $ Classifier.subclass_rfl
  case cons h t ih =>
    have ⟨_, ih1⟩ := ih
    have ⟨m, _⟩ := ih1.empty_excl_append_singleton (a:=h)
    exists 1 + m
    apply! excl_subclass_r $ .here Classifier.subclass_rfl

theorem Kind.Subtract.is_empty_l (he: IsEmpty K) : ∃ m K0, Subtract m K K1 K0 ∧ IsEmpty K0 := by
  induction he
  case empty =>
    exists 0, .empty
    apply And.intro .empty_l .empty
  case excl_super =>
    exists 0, .empty
    apply And.intro
    apply! excl_empty
    apply IsEmpty.empty
  case union ha hb =>
    have ⟨n1, R1, _, _⟩ := ha
    have ⟨n2, R2, _, _⟩ := hb
    exists 1 + max n1 n2, .union R1 R2
    apply And.intro; apply! union_l; apply! IsEmpty.union

theorem Kind.Subtract.rfl : ∃ m K1, Subtract m K K K1 ∧ IsEmpty K1 := by
  induction K
  case empty =>
    exists 0, .empty
    apply And.intro; apply empty_r;
    constructor
  case singleton r es =>
    have ⟨m, _⟩ := rfl_singleton (r:=r) (es:=es)
    exists m, .empty
    apply And.intro; assumption; constructor
  case union K1 K2 ih1 ih2 =>
    have ⟨m1, R1, h1, he1⟩ := ih1
    have ⟨m2, R2, h2, he2⟩ := ih2
    have ⟨k1, RK1, _, _⟩ := is_empty_l he1 (K1:=K2)
    have ⟨k2, RK2, _, _⟩ := is_empty_l he2 (K1:=K1)
    exists 1 + max (1 + max m1 k1) (1 + max m2 k2), .union RK1 RK2
    apply And.intro
    apply union_l
    apply! union_rl
    apply! union_rr
    constructor; assumption; assumption

theorem Kind.Subkind.rfl : Subkind K K := by
  have ⟨m, K, h, he⟩ := Subtract.rfl (K:=K)
  apply! subtract

theorem Kind.Subkind.refines_is_empty
  (hs : Subkind K1 K2)
  (he : IsEmpty K2) : IsEmpty K1 := by
  cases hs
  rename_i he1 hsub
  induction hsub
  case excl_empty => apply! IsEmpty.excl_super
  case subclass_l => cases he; rename_i he; cases he
  case excl_subclass_r hsc hsub ih =>
    apply ih _ he1


theorem Kind.Disjoint.is_empty_r
  (he : IsEmpty K)
  : Disjoint K1 K := by
  induction he
  case empty => apply! empty_r
  case excl_super => apply! excl_empty_r
  case union => apply! union_r

theorem Kind.Disjoint.refines_subkind'
  (hd : Disjoint K K2)
  (hs : Subtract n K1 K2 R)
  (he : IsEmpty R)
  : Disjoint K K1 := by
  induction hd generalizing n R
  case empty_l => apply! empty_l
  case empty_r =>
    cases hs
    case excl_empty => apply! excl_empty_r
    case empty_l => apply! empty_r
    case empty_r => apply! is_empty_r
    case union_l hs1 hs2 =>
      cases he
      apply union_r
      apply! refines_subkind' .empty_r
      apply! refines_subkind' .empty_r
  case excl_empty_l => apply! excl_empty_l
  case excl_empty_r hsc =>
    -- cases hs
    -- case excl_empty => apply! excl_empty_r
    -- case subclass_l => cases hsc
    -- case excl_subclass_r hsc2 hs =>
