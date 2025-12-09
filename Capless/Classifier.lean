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
        { subst_vars; left; apply Subclass.parent_l .rfl }
        { rename_i ih1; have ⟨m, ih1⟩ := ih1;
          generalize h : (n == m) = h0;
          cases h0
          right; right;
          apply Disjoint.refines_subclass_r; apply Disjoint.base (m:=m); aesop; assumption
          have h0 := LawfulBEq.eq_of_beq h; subst_vars; right; left; assumption
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

inductive Intersect : Kind -> Kind -> Kind -> Prop where
  | empty_l : Intersect .empty K .empty
  | empty_r : Intersect K .empty .empty
  | union_l : Intersect K1 K R1 -> Intersect K2 K R2 -> Intersect (K1.union K2) K (R1.union R2)
  | union_r : Intersect K K1 R1 -> Intersect K K2 R2 -> Intersect K (K1.union K2) (R1.union R2)
  | singleton_l : r1.Subclass r2 -> Intersect (.node r1 ex1) (.node r2 ex2) (.node r1 (ex1 ++ ex2))
  | singleton_r : r2.Subclass r1 -> Intersect (.node r1 ex1) (.node r2 ex2) (.node r2 (ex1 ++ ex2))
  | singleton_disj : r1.Disjoint r2 -> Intersect (.node r1 ex1) (.node r2 ex2) .empty

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
    r2.Subclass a -> -- (B \ a) is just empty
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
    r1.Subclass a ->  -- B \ C excludes the entirety of A
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
    cases r2.subclass_or_disjoint head
    case inl hs =>
      exists node r1 ex1
      apply! excl_absurd_r
    case inr hs =>
      cases hs
      case inl hs =>
        cases r1.subclass_or_disjoint head
        case inl hs1 => exists node r1 ex1; apply! excl_subclass_l
        case inr hs1 =>
          cases hs1
          case inl hs1 =>
            have ⟨R1, h⟩ := ih
            exists .union R1 (.node head ex1)
            apply excl_subclass_r


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
      have ⟨r1, h1⟩ := hb1 (a := node r1 ex1)
      have ⟨r2, h2⟩ := hb2 (a := r1)
      exists r2; apply! union_r
    case union ha1 ha2 =>
      have ⟨r1, h1⟩ := ha1
      have ⟨r2, h2⟩ := ha2
      exists .union r1 r2
      apply! union_l





theorem Kind.Subkind.trans (hs1 : Subkind K1 K2) (hs2 : Subkind K2 K3)  : Subkind K1 K2 := by
  cases hs1
  cases hs2
  rename_i


-- theorem Kind.Subkind.empty_l : Subkind .empty K := by
--   constructor
--   constructor
--   constructor

-- theorem Kind.Subtract.union_r_inv (hs : Subtract K (.union K1 K2) R) : ∃ R1 R2, Subtract K K1 R1 ∧  Subtract R1 K2 R2 ∧ Subkind R2 R ∧ Subkind R R2 := by
--   cases hs
--   case empty_l =>
--     exists empty, empty
--     apply And.intro .empty_l
--     apply And.intro .empty_l
--     apply And.intro .empty_l
--     exact .empty_l
--   case union_l ha hb =>


-- theorem Kind.Subtract.rfl (hs : Subtract K K R) : IsEmpty R := by
--   cases hs
--   case empty_l => constructor
--   case union_l ha hb =>

-- theorem Kind.Intersect.is_subkind (hi : Intersect K1 K2 R) : Subkind R K1 ∧ Subkind R K2 := by
--   induction hi
--   case empty_l => apply And.intro <;> apply Subkind.empty_l
--   case empty_r => apply

--   induction hs generalizing K
--   case empty_l => exact .empty_l
--   case union_l ih1 ih2 =>
--     cases he with
--     | union he1 he2 => exact .union_l (ih1 hd he1) (ih2 hd he2)
--   case absurd_l hc => exact absurd_l' hc
--   case excl_subclass_r ex1 a r1 r2 ex2 _ hss hsc hs ih =>
--     generalize h : node r2 (a :: ex2) = L at hd
--     induction hd generalizing K2 <;> try cases h
--     case empty_r => apply! empty_r
--     case union_r ha hb => subst_vars; simp_all; apply! union_r ha hb
--     case absurd_l hsc =>
--       cases hsc
--       case here hsc => cases hss.antisymm hsc
--       case there hsc =>
--         cases hs.empty_r_inv he (.absurd hsc)
--         apply! absurd_l
--     case absurd_r => apply! absurd_r
--     case root hd =>
--       cases hs.empty_or_subroot he
--       case inl hsc => apply! absurd_l
--       case inr hss => apply root $ hd.refines_subclass_l hss
--     case excl_l hsc =>
--       cases hs.empty_or_subroot he
--       case inl hsc => apply! absurd_l
--       case inr hss => apply! excl_l $ hsc.trans_subclass hss
--     case excl_r hsc1 =>
--       cases hsc1
--       case here hsc1 => apply excl_r $ hsc.trans_subclass hsc1
--       case there hsc1 => apply ih _ he; apply! excl_r
--   case excl_disjoint_r r1 ex1 r2 ex2 _ a hss hd hs ih =>
--     simp_all
--     generalize h : node r2 (a :: ex2) = L at hd
--     induction hd generalizing K2 <;> try cases h
--     case empty_r => apply! empty_r
--     case union_r ha hb => subst_vars; simp_all; apply! union_r ha hb
--     case absurd_l hsc =>
--       cases hsc
--       case here hsc => cases hss.antisymm hsc
--       case there hsc =>
--         cases hs.empty_r_inv he (.absurd hsc)
--         apply! absurd_l
--     case absurd_r => apply! absurd_r
--     case root hd =>
--       cases hs.empty_or_subroot he
--       case inl hsc => apply! absurd_l
--       case inr hss => apply root $ hd.refines_subclass_l hss
--     case excl_l hsc =>
--       cases hs.empty_or_subroot he
--       case inl hsc => apply! absurd_l
--       case inr hss => apply! excl_l $ hsc.trans_subclass hss
--     case excl_r hsc1 =>
--       cases hsc1
--       case here hsc1 => apply root $ (hd.refines_subclass_l hsc1).symm
--       case there hsc1 => apply ih _; apply! excl_r
--   case excl_irrelevant_r r1 ex1 r2 ex2 _ a hd1 hs ih =>
--     simp_all
--     generalize h : node r2 (a :: ex2) = L at hd
--     induction hd generalizing K2 <;> try cases h
--     case empty_r => apply! empty_r
--     case union_r ha hb => subst_vars; simp_all; apply! union_r ha hb
--     case absurd_l hsc =>
--       cases hsc
--       case here hsc => cases hd1.symm.not_subclass hsc
--       case there hsc =>
--         cases hs.empty_r_inv he (.absurd hsc)
--         apply! absurd_l
--     case absurd_r => apply! absurd_r
--     case root hd =>
--       cases hs.empty_or_subroot he
--       case inl hsc => apply! absurd_l
--       case inr hss => apply root $ hd.refines_subclass_l hss
--     case excl_l hsc =>
--       cases hs.empty_or_subroot he
--       case inl hsc => apply! absurd_l
--       case inr hss => apply! excl_l $ hsc.trans_subclass hss
--     case excl_r hsc1 =>
--       cases hsc1
--       case here hsc1 => apply ih; apply root; apply hd1.symm.refines_subclass_r hsc1
--       case there hsc1 => apply ih _; apply! excl_r
--   case excl_r r1 ex1 r2 ex2 _ a hd1 hsc hs ih =>
--     cases he
--     rename_i he he1
--     cases he1
--     simp_all
--     rename_i he1
--     generalize h : node r2 (a :: ex2) = L at hd
--     induction hd generalizing K2 <;> try cases h
--     case empty_r.refl => apply! empty_r
--     case union_r.refl ha hb => subst_vars; simp_all; apply! union_r ha hb
--     case absurd_l.refl hsc =>
--       cases hsc
--       case here hsc => cases hd1.symm.not_subclass hsc
--       case there hsc =>
--         cases hs.empty_r_inv he (.absurd hsc)
--         apply! absurd_l
--     case absurd_r.refl => apply! absurd_r
--     case root.refl hd =>
--       cases hs.empty_or_subroot he
--       case inl hsc => apply! absurd_l
--       case inr hss => apply root $ hd.refines_subclass_l hss
--     case excl_l.refl hsc =>
--       cases hs.empty_or_subroot he
--       case inl hsc => apply! absurd_l
--       case inr hss => apply! excl_l $ hsc.trans_subclass hss
--     case excl_r.refl hsc1 =>
--       cases hsc1
--       case here hsc1 => apply ih; apply root; apply hd1.symm.refines_subclass_r hsc1
--       case there hsc1 => apply ih _; apply! excl_r
--   case subclass_l r1 ex1 r2 hs =>
--     cases he
--     rename_i he
--     cases he
--     case here he => cases hs.antisymm he; have h := hd.append_excl_l (ex1:=ex1); simp at h; assumption
--     case there => apply! absurd_l'
--   case subclass_r r1 ex1 r2 hs =>
--     generalize h : node r2 [] = L at hd
--     induction hd <;> try cases h
--     case empty_r => apply! empty_r
--     case union_r ha hb => simp_all; apply! union_r
--     case absurd_l hsc => cases hsc
--     case absurd_r => apply! absurd_r
--     case root hd => apply! root $ hd.refines_subclass_l _
--     case excl_l hsc => apply! excl_l $ hsc.trans_subclass _
--     case excl_r hsc => cases hsc
--   case irrelevant_r hd =>
--     cases he
--     apply! absurd_l'
--   case union_r ha hb =>

    -- have ⟨hl, hr⟩ := hd.union_l_inv
    -- simp_all
    -- apply ha hl



















-- theorem Kind.Disjoint.refine_subkind_l' (hd : K1.Disjoint (.node r2 ex2)) (hs : Subkind L K1) : L.Disjoint (.node r2 ex2) := by
--   induction hs with
--   | empty_l => exact .empty_l
--   | union_l _ _ ih1 ih2 => exact .union_l (ih1 hd) (ih2 hd)
--   | absurd_l ha =>
--     apply absurd_l' ha
--   | excl_subclass_r hss hc hs ih =>
--     cases hd
--     case absurd_l hc =>
--       cases hc
--       case here hc => cases hss.antisymm hc
--       case there hc =>


--   | excl_disjoint_r _ _ _ ih => exact ih (hd.excl_cons_l)
--   | excl_irrelevant_r _ _ ih => exact ih (hd.excl_cons_l)
--   | subclass_r hsub => exact hd.refine_subclass_node hsub
--   | @union_r K K1' R K2' hi hs' ih =>
--     have ⟨hd1, hd2⟩ := hd.union_l_inv
--     exact refine_union_r hi hs' hd1 hd2 ih

-- theorem Kind.Disjoint.excl_cons_l (hd : Disjoint (.node r1 (a :: ex1)) K2) : Disjoint (.node r1 ex1) K2 := by
--   cases hd with
--   | empty_r => exact .empty_r
--   | union_r hd1 hd2 => exact .union_r (excl_cons_l hd1) (excl_cons_l hd2)
--   | absurd_l ha =>
--     cases ha with
--     | here hs => exact .absurd_l (.here hs)
--     | there ha => exact .absurd_l ha
--   | absurd_r ha => exact .absurd_r ha
--   | root hd => exact .root hd
--   | excl_l ha => exact .excl_l ha
--   | excl_r ha =>
--     cases ha with
--     | here hs => exact .excl_r (.here hs)
--     | there ha => exact .excl_r ha

-- theorem Kind.Disjoint.refine_subclass_node (hsub : r1.Subclass r2) (hd : Disjoint (.node r2 []) K2) : Disjoint (.node r1 ex1) K2 := by
--   induction K2 with
--   | empty => exact .empty_r
--   | node r3 ex3 =>
--     cases hd with
--     | absurd_l ha => cases ha
--     | absurd_r ha => exact .absurd_r ha
--     | root hd => exact .root (hd.refines_subclass_l hsub)
--     | excl_l ha => exact .excl_l (ha.trans_subclass hsub)
--     | excl_r ha => cases ha
--   | union K2a K2b ih1 ih2 =>
--     cases hd with
--     | union_r hd1 hd2 => exact .union_r (ih1 hd1) (ih2 hd2)

-- -- Helper for union_r case: if K ⊆ K1' ∪ K2' via union_r, and both K1' and K2' are disjoint from K2, then K is disjoint from K2
-- -- We prove by induction on K
-- theorem Kind.Disjoint.refine_union_r
--     (hi : Intersect K K1' R) (hs : Subkind R K2') (hd1 : K1'.Disjoint K2) (hd2 : K2'.Disjoint K2)
--     (ih : ∀ K2, K2'.Disjoint K2 → R.Disjoint K2) : K.Disjoint K2 := by
--   induction K generalizing K1' R K2' K2 with
--   | empty => exact .empty_l
--   | union Ka Kb iha ihb =>
--     cases hi with
--     | union_l hia hib =>
--       have ⟨hra, hrb⟩ := hs.union_l_inv
--       have iha' := iha hia hra.1 hd1 hd2 (fun K2 hd2' => (ih K2 hd2').union_l_inv.1)
--       have ihb' := ihb hib hrb.1 hd1 hd2 (fun K2 hd2' => (ih K2 hd2').union_l_inv.2)
--       exact .union_l iha' ihb'
--   | node r ex =>
--     cases hi with
--     | empty_r =>
--       -- K1' = .empty, R = .empty
--       -- hd1 : .empty.Disjoint K2
--       -- hd2 : K2'.Disjoint K2
--       -- hs : Subkind .empty K2'
--       -- We need (.node r ex).Disjoint K2
--       -- This case is actually impossible to prove in general!
--       -- Unless we have more information about the relationship between K and K2'
--       sorry
--     | singleton_l hsub =>
--       -- K1' = .node r2 ex2, R = .node r (ex ++ ex2)
--       -- r.Subclass r2
--       cases K2 with
--       | empty => exact .empty_r
--       | node r3 ex3 =>
--         cases hd1 with
--         | absurd_l ha => exact .absurd_l (ha.trans_subclass hsub)
--         | absurd_r ha => exact .absurd_r ha
--         | root hd => exact .root (hd.refines_subclass_l hsub)
--         | excl_l ha => exact .excl_l (ha.trans_subclass hsub)
--         | excl_r ha => exact .excl_r ha
--       | union K2a K2b =>
--         have ⟨hd1a, hd1b⟩ := hd1.union_r_inv
--         have ⟨hd2a, hd2b⟩ := hd2.union_r_inv
--         exact .union_r (refine_union_r (.singleton_l hsub) hs hd1a hd2a (fun K2 hd2' => ih K2 hd2'))
--                        (refine_union_r (.singleton_l hsub) hs hd1b hd2b (fun K2 hd2' => ih K2 hd2'))
--     | singleton_r hsub =>
--       -- K1' = .node r2 ex2, R = .node r2 (ex ++ ex2)
--       -- r2.Subclass r
--       cases K2 with
--       | empty => exact .empty_r
--       | node r3 ex3 =>
--         -- The intersection took r2, but K has r with r2 ⊆ r
--         -- We need K.Disjoint K2, but K might be strictly bigger than the intersection
--         cases hd2 with
--         | absurd_l ha =>
--           -- K2' is absurd, so R (which is a subkind of K2') must be absurd too
--           -- But R = .node r2 (ex ++ ex2), so we need ContainsSupOf (ex ++ ex2) r2
--           -- which would make R absurd. If R is absurd, then from the subkind
--           -- we can derive things...
--           sorry
--         | absurd_r ha => exact .absurd_r ha
--         | root hd =>
--           -- hd : r2'.Disjoint r3 where r2' is root of K2'
--           -- We need r.Disjoint r3, given r2.Subclass r
--           sorry
--         | excl_l ha =>
--           sorry
--         | excl_r ha => exact .excl_r ha
--       | union K2a K2b =>
--         sorry
--     | singleton_disj hdisj =>
--       -- r.Disjoint r2, so intersection is empty
--       -- R = .empty
--       -- But we need K = .node r ex to be disjoint from K2
--       -- We can't conclude this from K1'.Disjoint K2 alone
--       sorry

-- theorem Kind.Disjoint.refine_subkind_l (hd : K1.Disjoint K2) (hs : Subkind L K1) : L.Disjoint K2 := by
--   induction hs generalizing K2 with
--   | empty_l => exact .empty_l
--   | union_l _ _ ih1 ih2 => exact .union_l (ih1 hd) (ih2 hd)
--   | absurd_l ha => exact .absurd_l ha
--   | excl_subclass_r _ _ _ ih => exact ih (hd.excl_cons_l)
--   | excl_disjoint_r _ _ _ ih => exact ih (hd.excl_cons_l)
--   | excl_irrelevant_r _ _ ih => exact ih (hd.excl_cons_l)
--   | subclass_r hsub => exact hd.refine_subclass_node hsub
--   | @union_r K K1' R K2' hi hs' ih =>
--     have ⟨hd1, hd2⟩ := hd.union_l_inv
--     exact refine_union_r hi hs' hd1 hd2 ih

-- theorem Kind.Disjoint.refine_subkind_r (hd : Disjoint K1 K2) (hs : Subkind L K2) : K1.Disjoint L := by apply (hd.symm.refine_subkind_l hs).symm

-- theorem Kind.Disjoint.refine

-- inductive Kind : Type where
-- -- | empty : Kind
-- | singleton : Classifier -> List Classifier -> Kind
-- -- | union : Kind -> Kind -> Kind

-- @[simp]
-- def Kind.classifier (c : Classifier) := singleton c []

-- @[simp]
-- def Kind.excl (k : Kind) c :=
--   match k with
--   | singleton r es => singleton r (c :: es)


-- inductive HasSuperclassOf : Classifier -> List Classifier -> Prop where
--   | here : b.Subclass a -> HasSuperclassOf b (a :: xs)
--   | there : HasSuperclassOf b xs -> HasSuperclassOf b (a :: xs)

-- theorem HasSuperclassOf.subclass (hsc : HasSuperclassOf a es) (hs : Classifier.Subclass b a) : HasSuperclassOf b es := by
--   induction hsc
--   case here hsub => apply here  $ hs.trans hsub
--   case there ih => apply! there

-- inductive Kind.Disjoint : Kind -> Kind -> Prop where
--   -- | empty_l : Disjoint .empty K
--   -- | empty_r : Disjoint K .empty
--   -- empty classifiers are disjoint with everything else
--   | absurd_l : HasSuperclassOf a es -> Disjoint (singleton a es) K2
--   | absurd_r : HasSuperclassOf a es -> Disjoint K1 (singleton a es)
--   -- Otherwise, the root has to be a subclass of the other's exclude list
--   | root_l : HasSuperclassOf r1 es2 -> Disjoint (singleton r1 es1) (singleton r2 es2)
--   | root_r : HasSuperclassOf r2 es1 -> Disjoint (singleton r1 es1) (singleton r2 es2)
--   | root : Classifier.Disjoint r1 r2 -> Disjoint (singleton r1 es1) (singleton r2 es2)
--   -- union case
--   -- | union_l : Disjoint K1 K -> Disjoint K2 K -> Disjoint (K1.union K2) K
--   -- | union_r : Disjoint K K1 -> Disjoint K K2 -> Disjoint K (K1.union K2)

-- inductive Kind.Subkind : Kind -> Kind -> Prop where
--   | absurd_l : HasSuperclassOf a es ->
--     Subkind (singleton a es) K
--   -- | empty_l : Subkind .empty K
--   | subclass_no_excl :
--     r1.Subclass r2 ->
--     Subkind (singleton r1 es1) (singleton r2 [])
--   | excl_subclass :
--     Subkind (singleton r1 es1) (singleton r2 es2) ->
--     a.StrictSub r2 ->
--     HasSuperclassOf a es1 ->
--     Subkind (singleton r1 es1) (singleton r2 (a :: es2))
--   | excl_disjoint :
--     Subkind (singleton r1 es1) (singleton r2 es2) ->
--     a.StrictSub r2 ->
--     a.Disjoint r1 ->
--     Subkind (singleton r1 es1) (singleton r2 (a :: es2))
--   | excl_irrelevant :
--     Subkind (singleton r1 es1) (singleton r2 es2) ->
--     a.Disjoint r2 ->
--     Subkind (singleton r1 es1) (singleton r2 (a :: es2))

-- theorem Kind.Subkind.singleton_weaken_l (hs : Subkind (.singleton a es) K) : Subkind (.singleton a (e :: es)) K := by
--   cases hs
--   case absurd_l => apply! absurd_l $ .there _
--   case subclass_no_excl hsub => apply! subclass_no_excl
--   case excl_subclass hss hsc hs => apply! hs.singleton_weaken_l.excl_subclass _ (.there _)
--   case excl_disjoint hss hd hs => apply! hs.singleton_weaken_l.excl_disjoint
--   case excl_irrelevant hd hs => apply! hs.singleton_weaken_l.excl_irrelevant


-- theorem Kind.Subkind.rfl : Subkind K K := by
--   cases K
--   case singleton r es =>
--     induction es
--     case nil => apply subclass_no_excl .rfl
--     case cons h t ih =>
--       cases Classifier.subclass_or_disjoint r h
--       case inl hsub =>
--         apply! absurd_l $ .here _
--       case inr hsub =>
--         cases hsub
--         case inl hsub =>
--           cases hsub.might_strict
--           case inl he =>  subst_vars; apply! absurd_l $ .here _
--           case inr hsub => apply ih.singleton_weaken_l.excl_subclass hsub (.here .rfl)
--         case inr hd =>  apply ih.singleton_weaken_l.excl_irrelevant hd.symm

-- -- theorem Kind.Subkind.refines_is_empty
-- --   (hs : Subkind K1 K2)
-- --   (he : IsEmpty K2) : IsEmpty K1 := by
-- --   cases hs
-- --   rename_i he1 hsub
-- --   induction hsub <;> try cases he.singleton_must_excl
-- --   case absurd_l => apply! IsEmpty.absurd
-- --   case absurd_r => assumption
-- --   case empty_l => assumption
-- --   case empty_r => assumption
-- --   case excl_subclass_r hsub hsc hs ih =>
-- --     cases he
-- --     rename_i he
-- --     cases he
-- --     case here he => have h := hsub.antisymm he; contradiction
-- --     case there he => apply ih (.absurd he) he1
-- --   case excl_disjoint_r hsub hsc hs ih =>
-- --     cases he.singleton_cases
-- --     case inl he => have h := hsub.antisymm he; contradiction
-- --     case inr he => apply ih (.absurd he) he1
-- --   case excl_irrelevant_r hsub hs ih =>
-- --     cases he.singleton_cases
-- --     case inl he => have h := hsub.symm.not_subclass he; contradiction
-- --     case inr he => apply ih (.absurd he) he1
-- --   case residue hsc hs hsub ih =>
-- --     cases he.singleton_cases
-- --     case inl he => have h := hsc.antisymm he; contradiction
-- --     case inr he => cases he1; apply! ih (.absurd he)
-- --   case union_l hsa hsb iha ihb =>
-- --     cases he1
-- --     constructor
-- --     apply! iha
-- --     apply! ihb
-- --   case union_rl ha hb iha ihb =>
-- --     cases he
-- --     apply! iha _ (ihb _ he1)
-- --   case union_rr ha hb iha ihb =>
-- --     cases he
-- --     apply! iha _ (ihb _ he1)

-- -- theorem Kind.Disjoint.is_empty_r
-- --   (he : IsEmpty K)
-- --   : Disjoint K1 K := by
-- --   induction he
-- --   case empty => apply! empty_r
-- --   case absurd => apply! absurd_r
-- --   case union => apply! union_r

-- theorem Kind.Disjoint.symm (hd : Disjoint K1 K2) : Disjoint K2 K1 := by
--   induction hd
--   -- case empty_l => apply! empty_r
--   -- case empty_r => apply! empty_l
--   case absurd_l => apply! absurd_r
--   case absurd_r => apply! absurd_l
--   case root_l => apply! root_r
--   case root_r => apply! root_l
--   case root h => apply! root h.symm
--   -- case union_l => apply! union_r
--   -- case union_r => apply! union_l

-- theorem Kind.Subkind.absurd_r
--   (hs : Subkind (singleton r1 es1) (singleton r2 es2))
--   (hsc : HasSuperclassOf r2 es2)
--   : HasSuperclassOf r1 es1 := by
--   cases hs
--   case absurd_l => assumption
--   case subclass_no_excl => cases hsc
--   case excl_subclass hsc1 hss hs =>
--     cases hsc
--     case here hsub => cases hss.antisymm hsub
--     case there hsc => apply hs.absurd_r hsc
--   case excl_disjoint hd hss hs =>
--     cases hsc
--     case here hsub => cases hss.antisymm hsub
--     case there hsc => apply hs.absurd_r hsc
--   case excl_irrelevant hd hs =>
--     cases hsc
--     case here hsub => cases hd.symm.not_subclass hsub
--     case there hsc => apply hs.absurd_r hsc

-- theorem Kind.Subkind.root_is_subclass (hs : Subkind (singleton r1 es1) (singleton r2 es2)) : HasSuperclassOf r1 es1 ∨ r1.Subclass r2 := by
--   cases hs
--   case absurd_l => left; assumption
--   case subclass_no_excl => right; assumption
--   case excl_subclass hsc hss hs =>
--     cases hs.root_is_subclass <;> aesop
--   case excl_disjoint hs =>
--     cases hs.root_is_subclass <;> aesop
--   case excl_irrelevant hs =>
--     cases hs.root_is_subclass <;> aesop

-- theorem Kind.Subkind.refine_has_superclass
--   (hs : Subkind (singleton r1 es1) (singleton r2 es2))
--   (hsc : HasSuperclassOf a es2)
--   : HasSuperclassOf r1 es1 ∨ r1.Disjoint a ∨ HasSuperclassOf a es1 := by
--   cases hs
--   case absurd_l => aesop
--   case subclass_no_excl => cases hsc
--   case excl_subclass hsc hss hs =>
--     cases hsc
--     case here hsub => have h := hsc.subclass hsub; aesop
--     case there hsc => apply hs.refine_has_superclass hsc
--   case excl_disjoint hd hss hs =>
--     cases hsc
--     case here hsub => have h:= (hd.refines_subclass_l hsub).symm; aesop
--     case there hsc => apply hs.refine_has_superclass hsc
--   case excl_irrelevant hd hs =>
--     cases hsc
--     case here hsub =>
--       cases hs.root_is_subclass
--       case inl => aesop
--       case inr hsub2 => have h := ((hd.refines_subclass_l hsub).refines_subclass_r hsub2).symm; aesop
--     case there hsc => apply hs.refine_has_superclass hsc

-- theorem Kind.Disjoint.refine_by_subkind
--   (hd : Disjoint K2 L)
--   (hs : Subkind K1 K2)
--   : Disjoint K1 L := by
--   induction hs generalizing L
--   case absurd_l => apply! absurd_l
--   case subclass_no_excl hsub =>
--     cases hd
--     case absurd_l hsc => cases hsc
--     case absurd_r hsc => apply! absurd_r
--     case root_l hsc => apply! root_l $ hsc.subclass _
--     case root_r hsc =>  cases hsc
--     case root hd => apply! root $ hd.refines_subclass_l _
--   case excl_subclass hs hss hsc ih =>
--     cases hd
--     case absurd_l hsc =>
--       cases hsc
--       case here hsub => cases hss.antisymm hsub
--       case there hsc => apply absurd_l $ hs.absurd_r hsc
--     case absurd_r => apply! absurd_r
--     case root_l hsc1 =>
--       cases hs.root_is_subclass
--       case inl => apply! absurd_l
--       case inr hsub => apply! root_l $ hsc1.subclass _
--     case root_r hsc1 =>
--       cases hsc1
--       case here hsub => apply! root_r $ hsc.subclass _
--       case there hsc1 =>
--         cases hs.refine_has_superclass hsc1
--         case inl => apply! absurd_l
--         case inr h1 =>
--           cases h1
--           case inl h1 => apply! root
--           case inr h1 => apply! root_r
--     case root hd =>
--       cases hs.root_is_subclass
--       case inl => apply! absurd_l
--       case inr h1 => apply! root $ hd.refines_subclass_l _
--   case excl_disjoint hs hss hd1 ih =>
--     cases hd
--     case absurd_l hsc =>
--       cases hsc
--       case here hsub => cases hss.antisymm hsub
--       case there hsc => apply absurd_l $ hs.absurd_r hsc
--     case absurd_r => apply! absurd_r
--     case root_l hsc1 =>
--       cases hs.root_is_subclass
--       case inl => apply! absurd_l
--       case inr hsub => apply! root_l $ hsc1.subclass _
--     case root_r hsc1 =>
--       cases hsc1
--       case here hsub => apply! root $ hd1.symm.refines_subclass_r _
--       case there hsc1 =>
--         cases hs.refine_has_superclass hsc1
--         case inl => apply! absurd_l
--         case inr h1 =>
--           cases h1
--           case inl h1 => apply! root
--           case inr h1 => apply! root_r
--     case root hd2 =>
--       cases hs.root_is_subclass
--       case inl => apply! absurd_l
--       case inr => apply! root $ hd2.refines_subclass_l _
--   case excl_irrelevant hs hd ih =>
--     cases hd
--     case absurd_l hsc =>
--       cases hsc
--       case here hsub => cases hd.symm.not_subclass hsub
--       case there hsc => apply absurd_l $ hs.absurd_r hsc
--     case absurd_r => apply! absurd_r
--     case root_l hsc1 =>
--       cases hs.root_is_subclass
--       case inl => apply! absurd_l
--       case inr hsub => apply! root_l $ hsc1.subclass _
--     case root_r hsc1 =>
--       cases hsc1
--       case here hsub =>
--         cases hs.root_is_subclass
--         case inl => apply! absurd_l
--         case inr hsub2 =>
--           apply root
--           apply Classifier.Disjoint.symm
--           apply! (hd.refines_subclass_l _).refines_subclass_r _
--       case there hsc1 =>
--         cases hs.refine_has_superclass hsc1
--         case inl => apply! absurd_l
--         case inr h1 =>
--           cases h1
--           case inl h1 => apply! root
--           case inr h1 => apply! root_r
--     case root hd2 =>
--       cases hs.root_is_subclass
--       case inl => apply! absurd_l
--       case inr => apply! root $ hd2.refines_subclass_l _

-- theorem Kind.Subkind.trans (ha : Subkind K1 K2) (hb : Subkind K2 K3) : Subkind K1 K3 := by
--   induction hb generalizing K1
--   case absurd_l hsc =>
--     apply absurd_l $ ha.absurd_r hsc
--   case subclass_no_excl hs =>
--     cases ha.root_is_subclass
--     case inl hsc => apply! absurd_l
--     case inr hsub => apply! subclass_no_excl $ hsub.trans _
--   case excl_subclass hk hss hsc ih =>
--     cases K1 with
--     | singleton r1 es1 =>
--       cases ha.refine_has_superclass hsc
--       case inl hsc2 => apply! absurd_l
--       case inr h =>
--         cases h
--         case inl hd => apply! excl_disjoint (ih _) _ hd.symm
--         case inr hsc2 => apply! excl_subclass (ih _) _ hsc2
--   case excl_disjoint hk hss hd ih =>
--     cases K1 with
--     | singleton r1 es1 =>
--       cases ha.root_is_subclass
--       case inl hsc => apply! absurd_l
--       case inr hsub => apply! excl_disjoint (ih _) _ $ hd.refines_subclass_r _
--   case excl_irrelevant hk hd ih =>
--     apply! excl_irrelevant (ih _) _

-- theorem Kind.subkind_disjoint_absurd (ha : Subkind K1 K2) (hb : Disjoint K1 K2) : HasSuperclassOf K1.1 K1.2 := by
--   induction ha
--   case absurd_l hsc => exact hsc
--   case subclass_no_excl hsub =>
--     cases hb
--     case absurd_l hsc => exact hsc
--     case absurd_r hsc => cases hsc
--     case root_l hsc => cases hsc
--     case root_r hsc => exact hsc.subclass hsub
--     case root hd => exact absurd hsub hd.not_subclass
--   case excl_subclass hs hss hsc ih =>
--     cases hb
--     case absurd_l hsc2 => exact hsc2
--     case absurd_r hsc2 =>
--       cases hsc2
--       case here hsub => exact (hss.antisymm hsub).elim
--       case there hsc2 => exact ih (.absurd_r hsc2)
--     case root_l hsc2 =>
--       cases hsc2
--       case here hsub => exact hsc.subclass hsub
--       case there hsc2 => exact ih (.root_l hsc2)
--     case root_r hsc2 => exact ih (.root_r hsc2)
--     case root hd => exact ih (.root hd)
--   case excl_disjoint hs hss hd ih =>
--     cases hb
--     case absurd_l hsc => exact hsc
--     case absurd_r hsc =>
--       cases hsc
--       case here hsub => exact (hss.antisymm hsub).elim
--       case there hsc => exact ih (.absurd_r hsc)
--     case root_l hsc =>
--       cases hsc
--       case here hsub => exact absurd hsub hd.symm.not_subclass
--       case there hsc => exact ih (.root_l hsc)
--     case root_r hsc => exact ih (.root_r hsc)
--     case root hd2 => exact ih (.root hd2)
--   case excl_irrelevant hs hd ih =>
--     cases hb
--     case absurd_l hsc => exact hsc
--     case absurd_r hsc =>
--       cases hsc
--       case here hsub => exact absurd hsub hd.symm.not_subclass
--       case there hsc => exact ih (.absurd_r hsc)
--     case root_l hsc =>
--       cases hsc
--       case here hsub =>
--         cases hs.root_is_subclass
--         case inl hsc2 => exact hsc2
--         case inr hsub2 => exact absurd hsub2 (hd.refines_subclass_l hsub).not_subclass
--       case there hsc => exact ih (.root_l hsc)
--     case root_r hsc => exact ih (.root_r hsc)
--     case root hd2 => exact ih (.root hd2)

-- theorem Kind.Subkind.absurd_disjoint (ha : Subkind K1 K2) (hb : Disjoint K1 K2) : Subkind K1 K3 := by
--   cases K1; exact .absurd_l (Kind.subkind_disjoint_absurd ha hb)

-- theorem Kind.Disjoint.absurd_subkind (hb : Disjoint K1 K2) (ha : Subkind K1 K2) : Disjoint K1 K3 := by
--   cases K1; exact .absurd_l (Kind.subkind_disjoint_absurd ha hb)
