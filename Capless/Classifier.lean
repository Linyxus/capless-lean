import Capless.Basic
import Capless.Tactics

namespace Capless

inductive Classifier : Type where
  | top : Classifier
  | child : Nat -> Classifier -> Classifier
deriving DecidableEq

def Classifier.control := child 0 .top

inductive Classifier.Subclass : Classifier -> Classifier -> Prop where
  | rfl : Subclass a a
  | parent_l : Subclass a b -> Subclass (child n a) b

inductive Classifier.StrictSub : Classifier -> Classifier -> Prop where
  | child : StrictSub (child n a) a
  | parent_l : StrictSub a b -> StrictSub (child n a) b

theorem Classifier.Subclass.might_strict (hs : Subclass a b) : a = b ∨ StrictSub a b := by
  induction hs
  case rfl => left; simp
  case parent_l hp ih =>
    right
    cases ih
    case inl => subst_vars; constructor
    case inr => apply! StrictSub.parent_l

theorem Classifier.StrictSub.weaken (hs : StrictSub a b) : Subclass a b := by
  induction hs
  case child => apply Subclass.parent_l .rfl
  case parent_l hp ih => apply Subclass.parent_l ih

theorem Classifier.StrictSub.size (hs : StrictSub a b) : sizeOf a > sizeOf b := by induction hs <;> (simp; try omega)

inductive Classifier.Disjoint : Classifier -> Classifier -> Prop where
  | base : n != m -> Disjoint (child n p) (child m p)
  | left : Disjoint a b -> Disjoint (child n a) b
  | right : Disjoint a b -> Disjoint a (child m b)

theorem Classifier.Subclass.of_top : Subclass a .top := by
  induction a
  case top => apply rfl
  case child n k ih => apply parent_l ih

theorem Classifier.Subclass.parent_r (hs : Subclass a (child n b)) : Subclass a b := by
  cases hs
  case rfl => apply parent_l rfl
  case parent_l hp =>
    apply parent_l hp.parent_r

theorem Classifier.Subclass.trans (h1 : Subclass a b) (h2 : Subclass b c) : Subclass a c := by
  induction h2
  case rfl => assumption
  case parent_l hp ih => apply ih h1.parent_r

theorem Classifier.Subclass.down_r (hs : Subclass a b) : a = b ∨ ∃ n, Subclass a (child n b) := by
  induction hs
  case rfl => simp
  case parent_l ih =>
    rename_i n _
    right
    cases ih
    case inl ih => subst_vars; exists n; constructor
    case inr ih =>
      have ⟨m, ih⟩ := ih
      exists m
      apply parent_l ih

theorem Classifier.Subclass.size (hs : Subclass a b) : sizeOf a ≥ sizeOf b := by
  induction hs <;> (simp; try omega)

theorem Classifier.Subclass.antisymm (h1 : Subclass a b) (h2 : Subclass b a) : a = b := by
  induction h1
  case rfl => simp
  case parent_l hp ih =>
    have hp1 := hp.size
    have h21 := h2.size
    simp at h21
    omega

theorem Classifier.StrictSub.antisymm (hs : StrictSub a b) (hs2 : Subclass b a) : False := by
  have h := hs.size
  have h2 := hs2.size
  omega

theorem Classifier.StrictSub.subclass_r (hss : StrictSub a b) (hs : Subclass b c) : StrictSub a c := by
  induction hss
  case child n a =>
    induction hs generalizing n
    case rfl => apply child
    case parent_l m k ih =>
      apply parent_l ih
  case parent_l n a ih =>
    apply! parent_l $ ih _

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
  case rfl => assumption
  case parent_l hs ih =>
    apply right $ ih hd

theorem Classifier.Disjoint.refines_subclass_l (hd : Disjoint a2 b) (hs : Subclass a1 a2) : Disjoint a1 b := by
  apply symm
  apply refines_subclass_r hd.symm hs

theorem Classifier.Disjoint.left_inv (hd : Disjoint (child n a) b) : Subclass b a ∨ Disjoint a b := by
  cases hd
  case base m _ => left; constructor; constructor;
  case left => right; assumption
  case right hd =>
    cases hd.left_inv
    case inl hd => left; constructor; assumption
    case inr hd => right; apply! right

theorem Classifier.Disjoint.not_subclass (hd : Disjoint a b) (hs : Subclass a b) : False := by
  induction a generalizing b
  case top =>
    induction b
    case top => cases hd
    case child n p ih => cases hs
  case child n p ih =>
    induction b
    case top => cases hs; cases hd; apply! ih
    case child m q ih2 =>
      cases hs
      case rfl =>
        cases hd
        case base => aesop
        case left hs => apply ih2 hs.symm $ .parent_l .rfl
        case right hs => apply ih2 hs $ .parent_l .rfl
      case parent_l hs =>
        cases hd
        case base => have h := hs.size; simp at h; omega
        case left => apply! ih
        case right hd =>
          cases hd.left_inv
          case inl hd =>
            have h := hs.parent_r.antisymm hd
            subst_vars
            have h := hs.size; simp at h; omega
          case inr hd =>
            apply ih (b:=q) hd hs.parent_r

theorem Classifier.Disjoint.to_subclass (hd : Disjoint a b) (hs : Subclass c b) : Disjoint a c := by
  induction hs
  case rfl => assumption
  case parent_l hp ih =>
    apply right
    apply ih hd

theorem Classifier.subclass_or_disjoint a b:
  Subclass a b ∨ StrictSub b a ∨ Disjoint a b := by
  induction a
  case top =>
    cases Subclass.of_top (a:=b).might_strict
    case inl => simp_all; left; exact .rfl
    case inr => aesop
  case child n k ih =>
    cases ih
    case inl ih =>
      left; constructor; assumption
    case inr ih =>
      cases ih
      case inl ih =>
        cases ih.weaken.down_r
        { subst_vars; left; apply Subclass.parent_l .rfl }
        { rename_i ih1; have ⟨m, ih1⟩ := ih1;
          generalize h : (n == m) = h0;
          cases h0
          right; right;
          apply Disjoint.refines_subclass_r; apply Disjoint.base (m:=m); aesop; assumption
          have h0 := LawfulBEq.eq_of_beq h; subst_vars
          cases ih1.might_strict
          . left; subst_vars; exact .rfl
          . aesop
        }
      case inr ih =>
        right; right; apply Disjoint.left ih

def Classifier.subclass (a : Classifier) (b : Classifier) :=
  if a == b then true
  else match a with
    | .top => false
    | .child n p => p.subclass b

theorem Classifier.subclass_is_Subclass : Subclass a b ↔ a.subclass b := by
  apply Iff.intro
  . intro hs
    induction hs
    case rfl => unfold subclass; simp
    case parent_l n p => unfold subclass; simp; right; assumption
  . intro hs
    unfold subclass at hs
    split at hs
    case isTrue h =>
      have h1 := LawfulBEq.eq_of_beq h
      subst_vars
      constructor
    case isFalse h =>
      split at hs
      . contradiction
      . rename_i p
        constructor
        rw [subclass_is_Subclass (a:=p)]
        assumption

def Classifier.disjoint (a : Classifier) (b : Classifier) :=
  match a with
  | .top => false
  | .child n p =>
    match b with
    | .top => false
    | .child m q =>
      if p == q then n != m
      else disjoint (.child n p) q || disjoint p (.child m q)

theorem Classifier.disjoint_is_Disjoint {a b : Classifier} : Disjoint a b ↔ a.disjoint b := by
  apply Iff.intro
  . intro hs
    induction hs with
    | base hne =>
      unfold disjoint
      simp [hne]
    | @left a' b' n ha ih =>
      unfold disjoint
      match b' with
      | .top => cases ha.not_subclass .of_top
      | .child m q =>
        simp only
        split
        . rename_i heq
          have h1 := LawfulBEq.eq_of_beq heq
          subst_vars
          cases ha.symm.not_subclass $ .parent_l .rfl
        . simp [ih]
    | @right a' b' m ha ih =>
      unfold disjoint
      match a' with
      | .top =>
        have : ∀ c, ¬ Disjoint top c := fun c h => by
          induction c with
          | top => cases h
          | child n p ih =>
            cases h with
            | right ha => exact ih ha
        exact absurd ha (this _)
      | .child n p =>
        simp only
        split
        . rename_i heq
          have heq' := LawfulBEq.eq_of_beq heq
          subst heq'
          cases ha.not_subclass $ .parent_l .rfl
        . simp [ih]
  . intro hs
    unfold disjoint at hs
    split at hs
    . cases hs
    . split at hs
      . cases hs
      . split at hs
        . rename_i h
          have h1 := LawfulBEq.eq_of_beq h
          subst_vars
          apply! Disjoint.base
        . simp at hs
          cases hs
          case inl hs =>
            apply Disjoint.right
            rw [disjoint_is_Disjoint]
            assumption
          case inr hs =>
            apply Disjoint.left
            rw [disjoint_is_Disjoint]
            assumption
termination_by sizeOf a + sizeOf b

-- **
-- Kinds
-- **

inductive Kind : Type where
  | empty : Kind
  | node : Classifier -> List Classifier -> Kind -- .only[K].except[K1, ..., Kn]
  | union : Kind -> Kind -> Kind

@[simp]
def Kind.top := node .top []

-- Shorthand notation for a subtree without exclusions
@[simp]
def Kind.classifier c := node c []

def Kind.sup (a: Kind) (b: Kind) : Kind := a.union b

def Kind.inf (a: Kind) (b: Kind) : Kind :=
  match a with
  | .empty => b
  | .union a1 a2 => union (a1.inf b) (a2.inf b)
  | .node r1 ex1 =>
    match b with
    | .empty => .empty
    | .union b1 b2 => union (inf (.node r1 ex1) b1) (inf (.node r1 ex1) b2)
    | .node r2 ex2 =>
      if r1.subclass r2 then .node r1 (ex1 ++ ex2)
      else if r2.subclass r1 then .node r2 (ex1 ++ ex2)
      else .empty

inductive ContainsSupOf : List Classifier -> Classifier -> Prop where
  | here : b.Subclass a -> ContainsSupOf (a :: xs) b
  | there : ContainsSupOf xs b -> ContainsSupOf (a :: xs) b

theorem ContainsSupOf.append_l (h : ContainsSupOf xs b) : ContainsSupOf (xs ++ ys) b := by
  induction h with
  | here hs => exact .here hs
  | there _ ih => exact .there ih

theorem ContainsSupOf.append_r (h : ContainsSupOf ys b) : ContainsSupOf (xs ++ ys) b := by
  induction xs with
  | nil => exact h
  | cons _ _ ih => exact .there ih

theorem ContainsSupOf.trans_subclass (h : ContainsSupOf xs a) (hs : b.Subclass a) : ContainsSupOf xs b := by
  induction h with
  | here hs' => exact .here (hs.trans hs')
  | there _ ih => exact .there (ih hs)

theorem ContainsSupOf.of_append (h : ContainsSupOf (xs ++ ys) b) : ContainsSupOf xs b ∨ ContainsSupOf ys b := by
  induction xs with
  | nil => exact .inr h
  | cons a xs ih =>
    cases h with
    | here hs => exact .inl (.here hs)
    | there h =>
      cases ih h with
      | inl h => exact .inl (.there h)
      | inr h => exact .inr h

inductive Kind.IsEmpty : Kind -> Prop where
  | empty : IsEmpty .empty
  | absurd : ContainsSupOf exs r -> IsEmpty (.node r exs)
  | union : IsEmpty K1 -> IsEmpty K2 -> IsEmpty (.union K1 K2)

theorem Kind.IsEmpty.is_absurd (he : IsEmpty (.node r exs)) : ContainsSupOf exs r := by
  cases he; assumption

inductive Kind.Intersect : Kind -> Kind -> Kind -> Prop where
  | empty_l : Intersect .empty K .empty
  | empty_r : Intersect K .empty .empty
  | union_l : Intersect K1 K R1 -> Intersect K2 K R2 -> Intersect (K1.union K2) K (R1.union R2)
  | union_r : Intersect K K1 R1 -> Intersect K K2 R2 -> Intersect K (K1.union K2) (R1.union R2)
  | singleton_l : r1.Subclass r2 -> Intersect (.node r1 ex1) (.node r2 ex2) (.node r1 (ex1 ++ ex2))
  | singleton_r : r2.Subclass r1 -> Intersect (.node r1 ex1) (.node r2 ex2) (.node r2 (ex1 ++ ex2))
  | singleton_disj : r1.Disjoint r2 -> Intersect (.node r1 ex1) (.node r2 ex2) .empty

@[simp]
def Kind.intersect (k : Kind) (l : Kind) : Kind :=
  match k with
  | .empty => .empty
  | .union k1 k2 => .union (k1.intersect l) (k2.intersect l)
  | .node r1 ex1 =>
    match l with
    | .empty => .empty
    | .union l1 l2 => .union ((node r1 ex1).intersect l1) ((node r1 ex1).intersect l2)
    | .node r2 ex2 =>
      if r1.subclass r2 then .node r1 (ex1 ++ ex2)
      else if r2.subclass r1 then .node r2 (ex1 ++ ex2)
      else .empty

theorem Kind.Intersect.lawful : Intersect K L (K.intersect L) := by
  induction K generalizing L
  case empty => unfold intersect; apply empty_l
  case union ha hb =>
    unfold intersect
    apply union_l ha hb
  case node r1 ex1 =>
    induction L
    case empty => unfold intersect; simp; apply empty_r
    case union ha hb => unfold intersect; simp; apply union_r ha hb
    case node r2 ex2 =>
      unfold intersect
      simp
      split
      . rename_i h
        rw [← Classifier.subclass_is_Subclass] at h
        apply! singleton_l
      . split
        . rename_i h
          rw [← Classifier.subclass_is_Subclass] at h
          apply! singleton_r
        . rename_i h1 h2
          rw [← Classifier.subclass_is_Subclass] at h1 h2
          cases Classifier.subclass_or_disjoint r1 r2 <;> try contradiction
          rename_i h3; cases h3
          case inl h3 => have h4 := h3.weaken; contradiction
          case inr h3 => apply! singleton_disj

theorem Kind.Intersect.top_r {K : Kind} : K.intersect .top = K := by
  induction K
  case empty => simp
  case union ha hb => simp_all
  case node r1 ex1 =>
    have h := Classifier.Subclass.of_top (a:=r1)
    rw [Classifier.subclass_is_Subclass] at h
    aesop

theorem Kind.Intersect.top_l {K : Kind} : Kind.top.intersect K = K := by
  induction K
  case empty => simp
  case union ha hb => aesop
  case node r1 ex1 =>
    have h := Classifier.Subclass.of_top (a:=r1)
    rw [Classifier.subclass_is_Subclass] at h
    simp
    split
    . rename_i h1; unfold Classifier.subclass at h1; simp_all
    . simp


inductive Kind.Subtract : Kind -> Kind -> Kind -> Prop where
  | empty_l : Subtract .empty K .empty
  | union_l : Subtract K1 K R1 -> Subtract K2 K R2 -> Subtract (.union K1 K2) K (.union R1 R2)
  | empty_r : Subtract (.node r1 ex1) .empty (.node r1 ex1)
  | union_r :
    Subtract (.node r1 ex1) K1 R1 ->
    Subtract R1 K2 R2 ->
    Subtract (.node r1 ex1) (.union K1 K2) R2
  -- The singleton cases
  -- Basically we follow a few broad strokes:
  -- - A \ (B \ C) = (A \ B) ∪ (A ∩ B ∩ C)
  -- - For B of the form (.node r []) (no exclusion):
  --   - If r < A, refine A
  --   - If r > A, empty
  --   - If r ⊥ A, A
  -- Base case first
  | tree : Subtract (.node r1 ex1) (.node r2 []) (.node r1 (r2 :: ex1))
  -- Exclusion case
  -- First, handle the cases where (B \ C) doesn't make sense
  | excl_absurd_r :
    r2.StrictSub a -> -- (B \ a) is just empty
    Subtract (.node r1 ex1) (.node r2 (a :: ex2)) (.node r1 ex1)
  | excl_irrelevant_r :
    r2.Disjoint a -> -- (B \ a) = B
    Subtract (.node r1 ex1) (.node r2 ex2) R ->
    Subtract (.node r1 ex1) (.node r2 (a :: ex2)) R
  -- Now, for cases where a is a subtree of r2
  -- We use the formula A \ (B \ C) = (A \ B) ∪ (A ∩ B ∩ C)
  | excl_subclass_r :
    a.Subclass r2 ->
    a.Subclass r1 -> -- A ∩ B ∩ C = a with all the exclusions
    Subtract (.node r1 ex1) (.node r2 ex2) R ->
    Subtract (.node r1 ex1) (.node r2 (a :: ex2)) (.union R (.node a ex1))
                                        -- ^ we'd need (ex1 ++ ex2) here to be exact,
                                        -- but if an element is in the ex2 subtree
                                        -- and not already excluded from A, it is part
                                        -- of (A \ B), so it's okay to keep anyway.
  | excl_subclass_l :
    a.Subclass r2 ->
    r1.StrictSub a ->  -- B \ C excludes the entirety of A
    Subtract (.node r1 ex1) (.node r2 (a :: ex2)) (.node r1 ex1)
  | excl_irrelevant_l :
    a.Subclass r2 ->
    r1.Disjoint a -> -- irrelevant exclusion, A ∪ B ∪ C = empty
    Subtract (.node r1 ex1) (.node r2 ex2) R ->
    Subtract (.node r1 ex1) (.node r2 (a :: ex2)) R

inductive Kind.Subkind : Kind -> Kind -> Prop where
  | subtract : Subtract K1 K2 R -> IsEmpty R -> Subkind K1 K2

theorem Kind.Subtract.is_empty_l (hs : Subtract K1 K2 R) (he : IsEmpty K1) : IsEmpty R := by
  induction hs
  case empty_l => constructor
  case union_l ha hb =>
    cases he
    apply! IsEmpty.union (ha _) (hb _)
  case empty_r => assumption
  case union_r ha hb =>
    apply hb
    apply! ha
  case tree => constructor; exact .there he.is_absurd
  case excl_absurd_r => assumption
  case excl_irrelevant_r ih => apply! ih
  case excl_subclass_r hs2 hs1 _ ih =>
    constructor; apply! ih;
    constructor; cases he
    apply! ContainsSupOf.trans_subclass
  case excl_subclass_l hs2 hs1 => assumption
  case excl_irrelevant_l ih => apply! ih


theorem Kind.Subtract.absurd_l (hs : Subtract (.node r1 ex1) K R) (hsc : ContainsSupOf ex1 r1) : IsEmpty R := by
  apply hs.is_empty_l
  constructor
  assumption

theorem Kind.Subtract.empty_implies_subclass
  (hs : Subtract (.node r1 ex1) (.node r2 ex2) R)
  (he : IsEmpty R)
  : ContainsSupOf ex1 r1 ∨ r1.Subclass r2 := by
  cases hs
  case tree =>
    cases he.is_absurd <;> aesop
  case excl_absurd_r => left; apply he.is_absurd
  case excl_irrelevant_r hs => apply hs.empty_implies_subclass he
  case excl_subclass_r hs =>
    cases he
    apply! hs.empty_implies_subclass
  case excl_subclass_l => left; apply he.is_absurd
  case excl_irrelevant_l hs => apply! hs.empty_implies_subclass

theorem Kind.Subtract.empty_r_inv (hs : Subtract K1 K2 R) (he : IsEmpty R) (hek2 : IsEmpty K2) : IsEmpty K1 := by
  induction hs
  case empty_l => constructor
  case union_l ha hb =>
    cases he
    constructor
    apply! ha
    apply! hb
  case empty_r => assumption
  case union_r ha hb =>
    cases hek2
    simp_all
  case tree => cases hek2.is_absurd
  case excl_absurd_r hs => assumption
  case excl_irrelevant_r hd hs ih =>
    cases hek2.is_absurd
    case here hsk => cases hd.not_subclass hsk
    case there hek2 => apply! ih _ (.absurd hek2)
  case excl_subclass_r hs2 hs1 hs ih =>
    cases he
    cases hek2.is_absurd
    case here hsk =>
      cases hs2.antisymm hsk
      rename_i h _
      cases hs.empty_implies_subclass h
      case inl => constructor; assumption
      case inr hsk2 => cases hsk2.antisymm hs1; assumption
    case there hsk => apply! ih _ (.absurd _)
  case excl_subclass_l => assumption
  case excl_irrelevant_l hs2 hd1 hs ih =>
    cases hek2.is_absurd
    case here hsa =>
      cases hs2.antisymm hsa
      cases hs.empty_implies_subclass he
      case inl h1 => exact .absurd h1
      case inr h1 => cases hd1.not_subclass h1
    case there hsc => apply ih he (.absurd hsc)

theorem Kind.Subkind.empty_r_inv (hs : Subkind K1 K2) (he : IsEmpty K2) : IsEmpty K1 := by
  cases hs
  apply! Subtract.empty_r_inv

inductive Kind.Disjoint : Kind -> Kind -> Prop where
  | empty_l: Disjoint .empty K
  | empty_r : Disjoint K .empty
  | union_l : Disjoint K1 K -> Disjoint K2 K -> Disjoint (K1.union K2) K
  | union_r : Disjoint K K1 -> Disjoint K K2 -> Disjoint K (K1.union K2)
  | absurd_l : ContainsSupOf ex1 r1 -> Disjoint (.node r1 ex1) (.node r2 ex2)
  | absurd_r : ContainsSupOf ex2 r2 -> Disjoint (.node r1 ex1) (.node r2 ex2)
  | root : r1.Disjoint r2 -> Disjoint (.node r1 ex1) (.node r2 ex2)
  | excl_l : ContainsSupOf ex2 r1 -> Disjoint (.node r1 ex1) (.node r2 ex2)
  | excl_r : ContainsSupOf ex1 r2 -> Disjoint (.node r1 ex1) (.node r2 ex2)

theorem Kind.Disjoint.union_l_inv (hd : Disjoint (K1.union K2) K) : Disjoint K1 K ∧ Disjoint K2 K := by
  generalize hk : Kind.union K1 K2 = K' at hd
  induction hd with
  | empty_l => cases hk
  | empty_r => exact ⟨.empty_r, .empty_r⟩
  | union_l hd1 hd2 =>
    cases hk
    exact ⟨hd1, hd2⟩
  | union_r hd1 hd2 ih1 ih2 =>
    have ⟨hd1', hd2'⟩ := ih1 hk
    have ⟨hd1'', hd2''⟩ := ih2 hk
    exact ⟨.union_r hd1' hd1'', .union_r hd2' hd2''⟩
  | absurd_l => cases hk
  | absurd_r => cases hk
  | root => cases hk
  | excl_l => cases hk
  | excl_r => cases hk

theorem Kind.Disjoint.union_r_inv (hd : Disjoint K (K1.union K2)) : Disjoint K K1 ∧ Disjoint K K2 := by
  generalize hk : Kind.union K1 K2 = K' at hd
  induction hd with
  | empty_l => exact ⟨.empty_l, .empty_l⟩
  | empty_r => cases hk
  | union_l hd1 hd2 ih1 ih2 =>
    have ⟨hd1', hd2'⟩ := ih1 hk
    have ⟨hd1'', hd2''⟩ := ih2 hk
    exact ⟨.union_l hd1' hd1'', .union_l hd2' hd2''⟩
  | union_r hd1 hd2 =>
    cases hk
    exact ⟨hd1, hd2⟩
  | absurd_l => cases hk
  | absurd_r => cases hk
  | root => cases hk
  | excl_l => cases hk
  | excl_r => cases hk

theorem Kind.Disjoint.implies_empty_intersect (hd : K1.Disjoint K2) (hi : Intersect K1 K2 R) : IsEmpty R := by
  induction hi with
  | empty_l => exact .empty
  | empty_r => exact .empty
  | union_l hi1 hi2 ih1 ih2 =>
    have ⟨hd1, hd2⟩ := hd.union_l_inv
    exact .union (ih1 hd1) (ih2 hd2)
  | union_r hi1 hi2 ih1 ih2 =>
    have ⟨hd1, hd2⟩ := hd.union_r_inv
    exact .union (ih1 hd1) (ih2 hd2)
  | singleton_l hs =>
    cases hd with
    | absurd_l ha => exact .absurd (.append_l ha)
    | absurd_r ha => exact .absurd (.append_r (ha.trans_subclass hs))
    | root hd => cases hd.not_subclass hs
    | excl_l ha => exact .absurd (.append_r ha)
    | excl_r ha => exact .absurd (.append_l (ha.trans_subclass hs))
  | singleton_r hs =>
    cases hd with
    | absurd_l ha => exact .absurd (.append_l (ha.trans_subclass hs))
    | absurd_r ha => exact .absurd (.append_r ha)
    | root hd => cases hd.symm.not_subclass hs
    | excl_l ha => exact .absurd (.append_r (ha.trans_subclass hs))
    | excl_r ha => exact .absurd (.append_l ha)
  | singleton_disj => exact .empty

theorem Kind.Disjoint.from_empty_intersect (hi : Intersect K1 K2 R) (he : IsEmpty R) : K1.Disjoint K2 := by
  induction hi with
  | empty_l => exact .empty_l
  | empty_r => exact .empty_r
  | union_l hi1 hi2 ih1 ih2 =>
    cases he with
    | union he1 he2 => exact .union_l (ih1 he1) (ih2 he2)
  | union_r hi1 hi2 ih1 ih2 =>
    cases he with
    | union he1 he2 => exact .union_r (ih1 he1) (ih2 he2)
  | singleton_l hs =>
    cases he with
    | absurd ha =>
      cases ha.of_append with
      | inl ha => exact .absurd_l ha
      | inr ha => exact .excl_l ha
  | singleton_r hs =>
    cases he with
    | absurd ha =>
      cases ha.of_append with
      | inl ha => exact .excl_r ha
      | inr ha => exact .absurd_r ha
  | singleton_disj hd => exact .root hd

theorem Kind.Disjoint.top_l (hd: Disjoint .top K) : IsEmpty K := by
  cases hd
  case empty_r => constructor
  case union_r ha hb => apply IsEmpty.union ha.top_l hb.top_l
  case absurd_l hsc => cases hsc
  case absurd_r hsc => constructor; assumption
  case root hd => cases hd.symm.not_subclass .of_top
  case excl_l hsc => constructor; apply hsc.trans_subclass .of_top
  case excl_r hsc => cases hsc

theorem Kind.Disjoint.symm (hd : K1.Disjoint K2) : Disjoint K2 K1 := by
  induction hd with
  | empty_l => exact .empty_r
  | empty_r => exact .empty_l
  | union_l _ _ ih1 ih2 => exact .union_r ih1 ih2
  | union_r _ _ ih1 ih2 => exact .union_l ih1 ih2
  | absurd_l ha => exact .absurd_r ha
  | absurd_r ha => exact .absurd_l ha
  | root hd => exact .root hd.symm
  | excl_l ha => exact .excl_r ha
  | excl_r ha => exact .excl_l ha

theorem Kind.Disjoint.append_excl_l (hd : Disjoint (.node r1 ex2) K) : Disjoint (.node r1 (ex1 ++ ex2)) K := by
  cases hd
  case empty_r => apply! empty_r
  case union_r ha hb => apply union_r ha.append_excl_l hb.append_excl_l
  case absurd_l ha => apply absurd_l ha.append_r
  case absurd_r => apply! absurd_r
  case root => apply! root
  case excl_l => apply! excl_l
  case excl_r ha => apply excl_r ha.append_r

theorem Kind.Disjoint.refine_subroot_l (hd : Disjoint (.node r1 ex1) K) (hs : r2.Subclass r1) : Disjoint (.node r2 ex1) K := by
  cases hd
  case empty_r => apply! empty_r
  case union_r ha hb => apply! union_r (ha.refine_subroot_l _) (hb.refine_subroot_l _)
  case absurd_l ha => apply! absurd_l $ ha.trans_subclass _
  case absurd_r => apply! absurd_r
  case root hdr => apply root; apply! hdr.refines_subclass_l _
  case excl_l hc => apply! excl_l $ hc.trans_subclass _
  case excl_r => apply! excl_r

-- If K1 is disjoint from K', and R is the intersection of K with K1, then R is disjoint from K'
theorem Kind.Disjoint.intersect_disjoint (hd : K1.Disjoint K') (hi : Intersect K K1 R) : R.Disjoint K' := by
  induction hi
  case empty_l => apply! empty_l
  case empty_r => apply! empty_l
  case union_l iha ihb => apply! union_l (iha _) (ihb _)
  case union_r iha ihb =>
    have ⟨_, _⟩ := hd.union_l_inv
    apply! union_l (iha _) (ihb _)
  case singleton_l hs => apply append_excl_l; apply! hd.refine_subroot_l _
  case singleton_r hs => apply hd.append_excl_l
  case singleton_disj hdr => apply empty_l

theorem Kind.Disjoint.absurd_l' (hs : ContainsSupOf ex1 r1) : Disjoint (.node r1 ex1) K := by
  induction K
  case empty => apply empty_r
  case node => apply! absurd_l
  case union ha hb => apply! union_r

theorem Kind.Disjoint.refine_subtract_l (hd : Disjoint K1 K) (hs : Subtract K1 K2 R) : Disjoint R K := by
  induction hs
  case empty_l => exact .empty_l
  case union_l ih1 ih2 =>
    have ⟨hd1, hd2⟩ := hd.union_l_inv
    exact .union_l (ih1 hd1) (ih2 hd2)
  case empty_r => assumption
  case union_r ih1 ih2 => exact ih2 (ih1 hd)
  case tree => apply! hd.append_excl_l (ex1 := [_])
  case excl_absurd_r => assumption
  case excl_irrelevant_r ih => apply! ih
  case excl_subclass_r hs1 _ ih =>
    apply Disjoint.union_l
    apply! ih
    apply! hd.refine_subroot_l
  case excl_subclass_l => assumption
  case excl_irrelevant_l ih => apply! ih

theorem Kind.Disjoint.append_l_disj_inv (hd : Disjoint (.node r1 (a :: ex1)) (.node r2 ex2)) (hda : a.Disjoint r2) : Disjoint (.node r1 ex1) (.node r2 ex2) := by
  cases hd
  case absurd_l hsc =>
    cases hsc
    case here hs => apply! root $ hda.refines_subclass_l _
    case there hsc => apply! absurd_l
  case absurd_r => apply! absurd_r
  case root => apply! root
  case excl_l hsc => apply! excl_l
  case excl_r hsc =>
    cases hsc
    case here hs => cases hda.symm.not_subclass hs
    case there => apply! excl_r

theorem Kind.Disjoint.append_l_contained_inv (hd : Disjoint (.node r1 (a :: ex1)) (.node r2 ex2)) (hsc: ContainsSupOf ex2 a) : Disjoint (.node r1 ex1) (.node r2 ex2) := by
  cases hd
  case absurd_l hsc =>
    cases hsc
    case here hs => apply! excl_l $ hsc.trans_subclass _
    case there hsc => apply! absurd_l
  case absurd_r => apply! absurd_r
  case root => apply! root
  case excl_l hsc => apply! excl_l
  case excl_r hsc =>
    cases hsc
    case here hs => apply! absurd_r $ hsc.trans_subclass _
    case there => apply! excl_r

theorem Kind.Disjoint.refine_disjoint_subtract_l_disjoint_root
  (hdr : Disjoint R K)
  (hs : Subtract (.node r1 ex1) (.node r2 ex2) R)
  (hd : r1.Disjoint r2)
  : Disjoint (.node r1 ex1) K := by
  cases hs
  case tree =>
    generalize h : node r1 (r2 :: ex1) = L at hdr
    induction hdr <;> try cases h
    case empty_r => apply! empty_r
    case union_r ha hb => simp_all; apply! union_r
    case absurd_l hsc =>
      cases hsc
      case here hs => cases hd.not_subclass hs
      case there hsc => apply! absurd_l
    case absurd_r => apply! absurd_r
    case root hd2 => apply! root
    case excl_l => apply! excl_l
    case excl_r hsc =>
      cases hsc
      case here hs => apply! root $ hd.refines_subclass_r _
      case there hsc => apply! excl_r
  case excl_absurd_r => assumption
  case excl_irrelevant_r hs => apply! hdr.refine_disjoint_subtract_l_disjoint_root
  case excl_subclass_r hs =>
    have ⟨hl, _⟩ := hdr.union_l_inv
    apply! hl.refine_disjoint_subtract_l_disjoint_root _ hd
  case excl_subclass_l => assumption
  case excl_irrelevant_l hs => apply! hdr.refine_disjoint_subtract_l_disjoint_root

theorem Kind.Disjoint.refine_disjoint_subtract_l_subroot
  (hdr : Disjoint R K)
  (hs : Subtract (.node r1 ex1) (.node r2 ex2) R)
  (hsub : r2.Subclass r1)
  (hd2 : Disjoint (.node r2 ex1) K)
  : Disjoint (.node r1 ex1) K := by
  cases hs
  case tree =>
    generalize h : node r1 (r2 :: ex1) = L at hdr
    induction hdr <;> try cases h
    case empty_r => apply! empty_r
    case union_r ha hb =>
      have ⟨_, _⟩ := hd2.union_r_inv
      simp_all
      apply! union_r
    case absurd_l hsc =>
      cases hsc
      case here hs2 => cases hsub.antisymm hs2; assumption
      case there => apply! absurd_l
    case absurd_r => apply! absurd_r
    case root => apply! root
    case excl_l => apply! excl_l
    case excl_r hsc =>
      cases hsc
      case here hs2 =>
        cases hd2
        case absurd_l => apply excl_r; apply! ContainsSupOf.trans_subclass
        case absurd_r => apply! absurd_r
        case root hd => cases hd.symm.not_subclass hs2
        case excl_l hsc => apply! absurd_r $ hsc.trans_subclass _
        case excl_r hsc => apply! excl_r
      case there hsc => apply! excl_r
  case excl_absurd_r => assumption
  case excl_irrelevant_r hs =>  apply! hdr.refine_disjoint_subtract_l_subroot
  case excl_subclass_r hs =>
    have ⟨hl, _⟩ := hdr.union_l_inv
    apply! hl.refine_disjoint_subtract_l_subroot
  case excl_subclass_l => assumption
  case excl_irrelevant_l hs => apply! hdr.refine_disjoint_subtract_l_subroot



theorem Kind.Disjoint.refine_disjoint_subtract_l (hd2 : Disjoint K2 K) (hs : Subtract K1 K2 R) (hdr : Disjoint R K) : Disjoint K1 K := by
  induction hs generalizing K
  case empty_l => apply empty_l
  case union_l ih1 ih2 =>
    have ⟨_, _⟩ := hdr.union_l_inv
    apply! union_l (ih1 _ _) (ih2 _ _)
  case empty_r => assumption
  case union_r ha hb =>
    have ⟨hl, hr⟩ := hd2.union_l_inv
    apply ha hl _
    apply hb hr hdr
  case tree r1 ex1 r2 =>
    generalize h : node r1 (r2 :: ex1) = L at hdr
    induction hdr <;> try cases h
    case empty_r => apply! empty_r
    case union_r ha hb =>
      have ⟨_, _⟩ := hd2.union_r_inv
      simp_all
      apply! union_r
    case absurd_l hsc =>
      cases hsc
      case here hs =>
        cases hd2
        case absurd_l hsc => cases hsc
        case absurd_r hsc => apply! absurd_r
        case root hd =>  apply root; apply! hd.refines_subclass_l _
        case excl_l hsc => apply excl_l; apply! hsc.trans_subclass
        case excl_r hsc => cases hsc
      case there hsc => apply! absurd_l
    case absurd_r => apply! absurd_r
    case root => apply! root
    case excl_l => apply! excl_l
    case excl_r hsc =>
      cases hsc
      case here hs =>
        cases hd2
        case absurd_r hsc => apply! absurd_r
        case root hd => cases hd.symm.not_subclass hs
        case excl_l hsc => apply absurd_r; apply! hsc.trans_subclass
        case excl_r hsc => cases hsc
        case absurd_l hsc => cases hsc
      case there hsc => apply! excl_r
  case excl_subclass_r r1 ex1 r2 ex2 _ a hss hsc hs ih =>
    have ⟨hdr1, hdr2⟩ := hdr.union_l_inv
    generalize h : node r2 (a :: ex2) = L at hd2
    induction hd2 generalizing K2 <;> try cases h
    case empty_r => apply! empty_r
    case union_r ha hb =>
      simp_all
      have ⟨_, _⟩ := hdr.union_r_inv
      have ⟨_, _⟩ := hdr1.union_r_inv
      have ⟨_, _⟩ := hdr2.union_r_inv
      apply! union_r (ha _ _ _) (hb _ _ _)
    case absurd_l hsc =>
      cases hsc
      case here hsc1 =>
        cases hss.antisymm hsc1
        apply! hdr1.refine_disjoint_subtract_l_subroot
      case there hsc =>
        apply ih _ hdr1
        apply! absurd_l
    case absurd_r => apply! absurd_r
    case root hd1 => apply ih (.root hd1) hdr1
    case excl_l hsc => apply! ih (.excl_l _)
    case excl_r hsc =>
      cases hsc
      case here hs =>
        cases hdr2
        case absurd_l hsc => apply! excl_r $ hsc.trans_subclass _
        case absurd_r => apply! absurd_r
        case root hd => cases hd.symm.not_subclass hs
        case excl_l hsc => apply! absurd_r $ hsc.trans_subclass _
        case excl_r => apply! excl_r
      case there hsc => apply! ih (excl_r _)
  case excl_absurd_r hs => assumption
  case excl_irrelevant_r r1 ex1 r2 ex2 _ a hd hs ih =>
    generalize h : node r2 (a :: ex2) = L at hd2
    induction hd2 generalizing K2 <;> try cases h
    case empty_r => apply! empty_r
    case union_r ha hb =>
      simp_all
      have ⟨_, _⟩ := hdr.union_r_inv
      apply! union_r (ha _) (hb _)
    case absurd_l hsc =>
      cases hsc
      case here hsc => cases hd.not_subclass hsc
      case there hsc =>
        apply ih _ hdr
        apply! absurd_l
    case absurd_r => apply! absurd_r
    case root hd1 => apply ih (.root hd1) hdr
    case excl_l hsc => apply! ih (.excl_l _)
    case excl_r hsc =>
      cases hsc
      case here hs => apply ih _ hdr; apply root; apply! hd.refines_subclass_r
      case there hsc => apply! ih (excl_r _)
  case excl_subclass_l hs2 hs1 => assumption
  case excl_irrelevant_l r1 ex1 r2 ex2 _ a hs2 hd1 hs ih =>
    generalize h : node r2 (a :: ex2) = L at hd2
    induction hd2 generalizing K2 <;> try cases h
    case empty_r => apply! empty_r
    case union_r ha hb =>
      simp_all
      have ⟨_, _⟩ := hdr.union_r_inv
      apply! union_r (ha _) (hb _)
    case absurd_l hsc =>
      cases hsc
      case here hsc =>
        cases hs2.antisymm hsc
        apply! hdr.refine_disjoint_subtract_l_disjoint_root hs
      case there hsc =>
        apply ih _ hdr
        apply! absurd_l
    case absurd_r => apply! absurd_r
    case root hd1 => apply ih (.root hd1) hdr
    case excl_l hsc => apply! ih (.excl_l _)
    case excl_r hsc =>
      cases hsc
      case here hs => apply root; apply! hd1.refines_subclass_r
      case there hsc => apply! ih (excl_r _)

theorem Kind.Disjoint.is_empty_l (he : IsEmpty K) : Disjoint K L := by
  induction he
  case empty => apply empty_l
  case absurd => apply! absurd_l'
  case union ha hb => apply! union_l

theorem Kind.Disjoint.refine_subkind_l' (hd : Disjoint K2 K) (hs : Subtract K1 K2 R) (he : IsEmpty R) : Disjoint K1 K := by
  apply refine_disjoint_subtract_l hd hs
  apply is_empty_l he

theorem Kind.Disjoint.refine_subkind_l (hd : Disjoint K2 K) (hs : Subkind K1 K2) : Disjoint K1 K := by
  cases hs
  apply! hd.refine_subkind_l'

theorem Kind.Subkind.refine_disjoint_l (hs : Subkind K1 K2) (hd : Disjoint K2 K) : Disjoint K1 K := hd.refine_subkind_l hs

theorem Kind.Subtract.exists' : ∃ R, Subtract (node r1 ex1) (node r2 ex2) R := by
  induction ex2
  case nil => exists node r1 (r2 :: ex1); apply tree
  case cons head tail ih =>
    cases head.subclass_or_disjoint r2
    case inl hs =>
      have ⟨R, h⟩ := ih
      cases head.subclass_or_disjoint r1
      case inl hs1 =>
        exists .union R (.node head ex1)
        apply! excl_subclass_r
      case inr hs1 =>
        cases hs1
        case inl hs1 =>
          exists node r1 ex1
          apply! excl_subclass_l
        case inr hs1 =>
          exists R
          apply! excl_irrelevant_l _ hs1.symm
    case inr hs =>
      cases hs
      case inl hs =>
        exists node r1 ex1
        apply! excl_absurd_r
      case inr hs =>
        have ⟨R, h⟩ := ih
        exists R
        apply! excl_irrelevant_r hs.symm

theorem Kind.Subtract.exists (a : Kind) (b: Kind) : ∃ R, Subtract a b R := by
  induction b generalizing a
  case empty =>
    induction a
    case empty => exists empty; apply! empty_l
    case node r1 ex1 => exists node r1 ex1; apply empty_r
    case union ha hb =>
      have ⟨r1, h1⟩ := ha
      have ⟨r2, h2⟩ := hb
      exists .union r1 r2
      apply! union_l
  case union hb1 hb2 =>
    induction a
    case empty => exists empty; apply! empty_l
    case node r1 ex1 =>
      have ⟨r1, h1⟩ := hb1 (a := node r1 ex1)
      have ⟨r2, h2⟩ := hb2 (a := r1)
      exists r2; apply! union_r
    case union ha1 ha2 =>
      have ⟨r1, h1⟩ := ha1
      have ⟨r2, h2⟩ := ha2
      exists .union r1 r2
      apply! union_l
  case node r2 ex2 =>
    induction a
    case empty => exists empty; apply! empty_l
    case node r1 ex1 =>
      apply exists'
    case union ha1 ha2 =>
      have ⟨r1, h1⟩ := ha1
      have ⟨r2, h2⟩ := ha2
      exists .union r1 r2
      apply! union_l

theorem Kind.Subtract.is_empty_append_l
  (hs : Subtract (.node r1 ex1) (.node r2 ex2) R)
  (he : IsEmpty R)
  (hs1 : Subtract (.node r1 (a :: ex1)) (.node r2 ex2) R1)
  : IsEmpty R1 := by
  induction ex2 generalizing R R1
  case nil =>
    cases hs1
    cases hs
    constructor
    cases he.is_absurd
    case here hs => apply! ContainsSupOf.here
    case there hsc => exact .there $ .there hsc
  case cons head tail ih =>
    cases hs
    case excl_absurd_r hs =>
      cases hs1
      case excl_absurd_r => constructor; cases he; apply! ContainsSupOf.there
      case excl_irrelevant_r hd hs1 => cases hd.not_subclass hs.weaken
      case excl_subclass_r hs1 hs2 hsa => cases hs.antisymm hs2
      case excl_subclass_l => constructor; cases he; apply! ContainsSupOf.there
      case excl_irrelevant_l hd hs2 hs1 => cases hs.antisymm hs2
    case excl_irrelevant_r hd hs =>
      cases hs1
      case excl_absurd_r hsub => cases hd.not_subclass hsub.weaken
      case excl_irrelevant_r hs1 => apply! ih
      case excl_subclass_r hsub1 hsub2 hs1 => cases hd.symm.not_subclass hsub2
      case excl_subclass_l hsub => cases hd.symm.not_subclass hsub
      case excl_irrelevant_l hsub _ => cases hd.symm.not_subclass hsub
    case excl_subclass_r hsub1 hsub2 hs =>
      cases he
      rename_i he1 he
      cases hs1
      case excl_absurd_r hsub =>
        constructor
        cases hsub.antisymm hsub2
      case excl_irrelevant_r hd hs1 => apply! ih
      case excl_subclass_r =>
        constructor
        . apply! ih
        . constructor; cases he; apply! ContainsSupOf.there
      case excl_subclass_l hsub _ => cases hsub.antisymm hsub1
      case excl_irrelevant_l hd _ _ => cases hd.symm.not_subclass hsub1
    case excl_subclass_l hsub1 hsub2 =>
      have ⟨R, h⟩ := Subtract.exists (node r1 ex1) (node r2 tail)
      have he1 := h.is_empty_l he
      cases hs1
      case excl_absurd_r => constructor; cases he; apply! ContainsSupOf.there
      case excl_irrelevant_r hd hs => cases hd.symm.not_subclass hsub2
      case excl_subclass_r hsub _ hs1 =>
        cases hsub.antisymm hsub1.weaken
        constructor
        . apply! ih
        . constructor; cases he; apply! ContainsSupOf.there
      case excl_subclass_l => constructor; cases he; apply! ContainsSupOf.there
      case excl_irrelevant_l hd _ _ => cases hd.not_subclass hsub1.weaken
    case excl_irrelevant_l hd hsub2 hs =>
      cases hs1
      case excl_absurd_r hsub => cases hsub.antisymm hsub2
      case excl_irrelevant_r hd2 hs => apply! ih
      case excl_subclass_r hsub1 _ hs1 => cases hd.symm.not_subclass hsub1
      case excl_subclass_l hsub1 _ => cases hd.not_subclass hsub1.weaken
      case excl_irrelevant_l hsub2 hs1 => apply! ih

theorem Kind.Subtract.unique
  (hs1 : Subtract K1 K2 R1)
  (hs2 : Subtract K1 K2 R2)
  : R1 = R2 := by
  induction hs1 generalizing R2
  case empty_l => cases hs2; simp
  case union_l ha hb =>
    cases hs2
    simp
    apply And.intro
    apply! ha
    apply! hb
  case empty_r => cases hs2; simp
  case union_r ha hb =>
    cases hs2
    case union_r ga gb => cases ha ga; apply! hb
  case tree => cases hs2; simp
  case excl_absurd_r hss =>
    cases hs2
    case excl_absurd_r => simp
    case excl_irrelevant_r hd _ => cases hd.not_subclass hss.weaken
    case excl_subclass_r hs _ => cases hss.antisymm hs
    case excl_subclass_l hs => cases hss.antisymm hs
    case excl_irrelevant_l hs _ => cases hss.antisymm hs
  case excl_irrelevant_r hd hs ih =>
    cases hs2
    case excl_absurd_r hss => cases hd.not_subclass hss.weaken
    case excl_irrelevant_r hs2 => apply! ih
    case excl_subclass_r hs _ => cases hd.symm.not_subclass hs
    case excl_subclass_l hs => cases hd.symm.not_subclass hs
    case excl_irrelevant_l hs _ => cases hd.symm.not_subclass hs
  case excl_subclass_r hsa hsb hs1 ih =>
    cases hs2
    case excl_absurd_r hss => cases hss.antisymm hsa
    case excl_irrelevant_r hd _ => cases hd.symm.not_subclass hsa
    case excl_subclass_r hs _ => simp; apply! ih
    case excl_subclass_l hss _ => cases hss.antisymm hsb
    case excl_irrelevant_l hd _ _ => cases hd.symm.not_subclass hsb
  case excl_subclass_l hsa hss =>
    cases hs2
    case excl_absurd_r hss => cases hss.antisymm hsa
    case excl_irrelevant_r hd _ => cases hd.symm.not_subclass hsa
    case excl_subclass_r hs _ _ => cases hss.antisymm hs
    case excl_subclass_l hss _ => simp
    case excl_irrelevant_l hd _ _ => cases hd.not_subclass hss.weaken
  case excl_irrelevant_l hs hd hs1 ih =>
    cases hs2
    case excl_absurd_r hss => cases hss.antisymm hs
    case excl_irrelevant_r hd _ => cases hd.symm.not_subclass hs
    case excl_subclass_r hs _ _ => cases hd.symm.not_subclass hs
    case excl_subclass_l hss _ => cases hd.not_subclass hss.weaken
    case excl_irrelevant_l hd _ _ => apply! ih

-- theorem Kind.Subtract.is_subkind
--   (hs : Subtract K1 K2 R)
--   : Subkind R K1 := by
--   induction hs
--   case empty_l => constructor; constructor; constructor
--   case union_l ha hb =>


theorem Kind.Subtract.empty_union_l
  (hs : Subtract (.union K1 K2) K R)
  (he : R.IsEmpty)
  (hs1 : Subtract K1 K R1)
  (hs2 : Subtract K2 K R2)
  : R1.IsEmpty ∧ R2.IsEmpty := by
  cases hs
  case union_l ha hb =>
    cases hs1.unique ha
    cases hs2.unique hb
    cases he
    aesop

theorem Kind.Subtract.empty_union_rl
  (hs : Subtract K K1 R)
  (he : R.IsEmpty)
  (hs1 : Subtract K (.union K1 K2) R1)
  : R1.IsEmpty := by
  cases hs1
  case empty_l => constructor
  case union_l C1 R1 C2 R2 ha hb =>
    have ⟨T1, h1⟩ := Subtract.exists C1 K1
    have ⟨T2, h2⟩ := Subtract.exists C2 K1
    have ⟨_, _⟩ := hs.empty_union_l he h1 h2
    constructor
    apply! h1.empty_union_rl
    apply! h2.empty_union_rl
  case union_r hsa hsb =>
    cases hs.unique hsa
    apply hsb.is_empty_l he

theorem Kind.Subtract.top (hs : Subtract K .top R) : IsEmpty R := by
  cases hs
  case empty_l => constructor
  case union_l ha hb =>
    apply IsEmpty.union ha.top hb.top
  case tree =>
    constructor
    apply ContainsSupOf.here
    apply Classifier.Subclass.of_top

theorem Kind.Subkind.of_top : Subkind K .top := by
  have ⟨R, h⟩ := Subtract.exists K .top
  apply subtract h h.top

-- prove later
theorem Kind.Subtract.rfl (hs : Subtract K K R) : IsEmpty R := by sorry

theorem Kind.Subkind.rfl : Subkind K K := by
  have ⟨R, h⟩ := Subtract.exists K K
  apply subtract h h.rfl

-- prove later
theorem Kind.Subtract.implies_trans
  (hs3 : Subtract K1 K3 R3)
  (hs1 : Subtract K1 K2 R1)
  (he1 : R1.IsEmpty)
  (hs2 : Subtract K2 K3 R2)
  (he2 : R2.IsEmpty)
  : R3.IsEmpty := by sorry

theorem Kind.Subkind.trans (hs1 : Subkind K1 K2) (hs2 : Subkind K2 K3) : Subkind K1 K3 := by
  cases hs1
  cases hs2
  rename_i h1 h2 _ h3 h4
  have ⟨R, h⟩ := Subtract.exists K1 K3
  apply subtract h
  apply! h.implies_trans h1

theorem Kind.Intersect.with_subkind
  (hs : K1.Subkind K2)
  : (intersect L K1).Subkind (intersect L K2) := by sorry

theorem Kind.Intersect.with_subkind_r
  (hs : K1.Subkind K2)
  : (intersect K1 L).Subkind (intersect K2 L) := by sorry

theorem Kind.Subkind.of_empty
  (hs : Subkind K L)
  (he : L.IsEmpty)
  : K.IsEmpty := by
  cases hs
  case subtract hs he1 => apply! hs.empty_r_inv

theorem Kind.Intersect.subkind_l
  : (intersect K L).Subkind K := by sorry
theorem Kind.Intersect.subkind_r
  : (intersect K L).Subkind L := by sorry

theorem Kind.Intersect.is_empty_l
  (he : IsEmpty K) : IsEmpty (K.intersect L) := by
  apply Subkind.of_empty subkind_l he

theorem Kind.Intersect.is_empty_r
  (he : IsEmpty L) : IsEmpty (intersect K L) := by
  apply Subkind.of_empty subkind_r he

theorem Kind.Subkind.union_rl : Subkind K1 (.union K1 K2) := by sorry
theorem Kind.Subkind.union_rr : Subkind K2 (.union K1 K2) := by sorry

theorem Kind.Subkind.union_l
  (hs1 : Subkind K1 L)
  (hs2 : Subkind K2 L)
  : Subkind (.union K1 K2) L := by
  cases hs1
  cases hs2
  constructor
  apply! Subtract.union_l
  apply! IsEmpty.union

theorem Kind.Subkind.join
  (hs1 : Subkind K1 L1)
  (hs2 : Subkind K2 L2)
  : Subkind (.union K1 K2) (.union L1 L2) := by
  apply union_l
  apply trans hs1 .union_rl
  apply trans hs2 .union_rr

theorem Kind.Subkind.reorder_union_4 : Subkind (.union (.union A B) (.union C D)) (.union (.union A C) (.union B D)) := by
  apply union_l
  . apply union_l
    . apply trans .union_rl .union_rl
    . apply trans .union_rl .union_rr
  . apply union_l
    . apply trans .union_rr .union_rl
    . apply trans .union_rr .union_rr

theorem Kind.Intersect.union_r_subkind : Subkind (.intersect K (.union L1 L2)) (.union (K.intersect L1) (K.intersect L2)) := by
  induction K
  case empty => simp; apply Subkind.subtract; apply Subtract.empty_l; constructor
  case node => simp; apply Subkind.rfl
  case union ha hb =>
    -- simp
    have h := Subkind.join ha hb
    simp at h
    simp
    apply Subkind.trans h .reorder_union_4

theorem Kind.Subkind.is_empty_l
  (he : IsEmpty K)
  : Subkind K L := by
  induction he
  case empty =>
    apply subtract .empty_l .empty
  case absurd exs r hsc =>
    have ⟨R, h⟩ := Subtract.exists (.node r exs) L
    apply! subtract h $ h.absurd_l _
  case union h1 h2 =>
    apply! union_l

theorem Kind.Intersect.union_r_superkind : Subkind (.union (K.intersect L1) (K.intersect L2)) (.intersect K (.union L1 L2)) := by
  induction K
  case empty => simp; apply Subkind.is_empty_l; constructor; constructor; constructor;
  case node => simp; apply Subkind.rfl
  case union ha hb =>
    have h := Subkind.join ha hb
    simp
    apply Subkind.trans .reorder_union_4 h

-- theorem Kind.Subkind.intersect_l_inv
--   (hs : Subkind (K1.intersect L) (K2.intersect L))
--   : Subkind K1 K2 := by

-- theorem Kind.Subkind.union_with_subkind_l
--   (hs : Subkind K L)
--   : Subkind (L.union K) L := by
--   apply union_l .rfl hs

theorem Kind.Intersect.union_l_subkind : Subkind (.intersect (.union K1 K2) L) (.union (K1.intersect L) (K2.intersect L)) := by sorry

theorem Kind.Intersect.assoc_subkind : Subkind (.intersect (.intersect K1 K2) K3) (.intersect K1 (.intersect K2 K3)) := by
  induction K1 <;> try simp_all
  case empty => apply Subkind.rfl
  case union ha hb => apply Subkind.join ha hb
  case node =>
    induction K2
    case empty => simp; apply Subkind.rfl
    case union ha hb => simp; apply Subkind.join ha hb
    case node => sorry

theorem Kind.Intersect.assoc_superkind : Subkind (.intersect K1 (.intersect K2 K3)) (.intersect (.intersect K1 K2) K3) := by
  induction K1 <;> try simp_all
  case empty => apply Subkind.rfl
  case union ha hb => apply Subkind.join ha hb
  case node =>
    induction K2
    case empty => simp; apply Subkind.rfl
    case union ha hb => simp; apply Subkind.join ha hb
    case node => sorry
