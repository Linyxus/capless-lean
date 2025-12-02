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


inductive Kind : Type where
-- | empty : Kind
| singleton : Classifier -> List Classifier -> Kind
-- | union : Kind -> Kind -> Kind

@[simp]
def Kind.classifier (c : Classifier) := singleton c []

@[simp]
def Kind.excl (k : Kind) c :=
  match k with
  | singleton r es => singleton r (c :: es)


inductive HasSuperclassOf : Classifier -> List Classifier -> Prop where
  | here : b.Subclass a -> HasSuperclassOf b (a :: xs)
  | there : HasSuperclassOf b xs -> HasSuperclassOf b (a :: xs)

theorem HasSuperclassOf.subclass (hsc : HasSuperclassOf a es) (hs : Classifier.Subclass b a) : HasSuperclassOf b es := by
  induction hsc
  case here hsub => apply here  $ hs.trans hsub
  case there ih => apply! there

inductive Kind.Disjoint : Kind -> Kind -> Prop where
  -- | empty_l : Disjoint .empty K
  -- | empty_r : Disjoint K .empty
  -- empty classifiers are disjoint with everything else
  | absurd_l : HasSuperclassOf a es -> Disjoint (singleton a es) K2
  | absurd_r : HasSuperclassOf a es -> Disjoint K1 (singleton a es)
  -- Otherwise, the root has to be a subclass of the other's exclude list
  | root_l : HasSuperclassOf r1 es2 -> Disjoint (singleton r1 es1) (singleton r2 es2)
  | root_r : HasSuperclassOf r2 es1 -> Disjoint (singleton r1 es1) (singleton r2 es2)
  | root : Classifier.Disjoint r1 r2 -> Disjoint (singleton r1 es1) (singleton r2 es2)
  -- union case
  -- | union_l : Disjoint K1 K -> Disjoint K2 K -> Disjoint (K1.union K2) K
  -- | union_r : Disjoint K K1 -> Disjoint K K2 -> Disjoint K (K1.union K2)

inductive Kind.Subkind : Kind -> Kind -> Prop where
  | absurd_l : HasSuperclassOf a es ->
    Subkind (singleton a es) K
  -- | empty_l : Subkind .empty K
  | subclass_no_excl :
    r1.Subclass r2 ->
    Subkind (singleton r1 es1) (singleton r2 [])
  | excl_subclass :
    Subkind (singleton r1 es1) (singleton r2 es2) ->
    a.StrictSub r2 ->
    HasSuperclassOf a es1 ->
    Subkind (singleton r1 es1) (singleton r2 (a :: es2))
  | excl_disjoint :
    Subkind (singleton r1 es1) (singleton r2 es2) ->
    a.StrictSub r2 ->
    a.Disjoint r1 ->
    Subkind (singleton r1 es1) (singleton r2 (a :: es2))
  | excl_irrelevant :
    Subkind (singleton r1 es1) (singleton r2 es2) ->
    a.Disjoint r2 ->
    Subkind (singleton r1 es1) (singleton r2 (a :: es2))

theorem Kind.Subkind.singleton_weaken_l (hs : Subkind (.singleton a es) K) : Subkind (.singleton a (e :: es)) K := by
  cases hs
  case absurd_l => apply! absurd_l $ .there _
  case subclass_no_excl hsub => apply! subclass_no_excl
  case excl_subclass hss hsc hs => apply! hs.singleton_weaken_l.excl_subclass _ (.there _)
  case excl_disjoint hss hd hs => apply! hs.singleton_weaken_l.excl_disjoint
  case excl_irrelevant hd hs => apply! hs.singleton_weaken_l.excl_irrelevant


theorem Kind.Subkind.rfl : Subkind K K := by
  cases K
  case singleton r es =>
    induction es
    case nil => apply subclass_no_excl .rfl
    case cons h t ih =>
      cases Classifier.subclass_or_disjoint r h
      case inl hsub =>
        apply! absurd_l $ .here _
      case inr hsub =>
        cases hsub
        case inl hsub =>
          cases hsub.might_strict
          case inl he =>  subst_vars; apply! absurd_l $ .here _
          case inr hsub => apply ih.singleton_weaken_l.excl_subclass hsub (.here .rfl)
        case inr hd =>  apply ih.singleton_weaken_l.excl_irrelevant hd.symm

-- theorem Kind.Subkind.refines_is_empty
--   (hs : Subkind K1 K2)
--   (he : IsEmpty K2) : IsEmpty K1 := by
--   cases hs
--   rename_i he1 hsub
--   induction hsub <;> try cases he.singleton_must_excl
--   case absurd_l => apply! IsEmpty.absurd
--   case absurd_r => assumption
--   case empty_l => assumption
--   case empty_r => assumption
--   case excl_subclass_r hsub hsc hs ih =>
--     cases he
--     rename_i he
--     cases he
--     case here he => have h := hsub.antisymm he; contradiction
--     case there he => apply ih (.absurd he) he1
--   case excl_disjoint_r hsub hsc hs ih =>
--     cases he.singleton_cases
--     case inl he => have h := hsub.antisymm he; contradiction
--     case inr he => apply ih (.absurd he) he1
--   case excl_irrelevant_r hsub hs ih =>
--     cases he.singleton_cases
--     case inl he => have h := hsub.symm.not_subclass he; contradiction
--     case inr he => apply ih (.absurd he) he1
--   case residue hsc hs hsub ih =>
--     cases he.singleton_cases
--     case inl he => have h := hsc.antisymm he; contradiction
--     case inr he => cases he1; apply! ih (.absurd he)
--   case union_l hsa hsb iha ihb =>
--     cases he1
--     constructor
--     apply! iha
--     apply! ihb
--   case union_rl ha hb iha ihb =>
--     cases he
--     apply! iha _ (ihb _ he1)
--   case union_rr ha hb iha ihb =>
--     cases he
--     apply! iha _ (ihb _ he1)

-- theorem Kind.Disjoint.is_empty_r
--   (he : IsEmpty K)
--   : Disjoint K1 K := by
--   induction he
--   case empty => apply! empty_r
--   case absurd => apply! absurd_r
--   case union => apply! union_r

theorem Kind.Disjoint.symm (hd : Disjoint K1 K2) : Disjoint K2 K1 := by
  induction hd
  -- case empty_l => apply! empty_r
  -- case empty_r => apply! empty_l
  case absurd_l => apply! absurd_r
  case absurd_r => apply! absurd_l
  case root_l => apply! root_r
  case root_r => apply! root_l
  case root h => apply! root h.symm
  -- case union_l => apply! union_r
  -- case union_r => apply! union_l

theorem Kind.Subkind.absurd_r
  (hs : Subkind (singleton r1 es1) (singleton r2 es2))
  (hsc : HasSuperclassOf r2 es2)
  : HasSuperclassOf r1 es1 := by
  cases hs
  case absurd_l => assumption
  case subclass_no_excl => cases hsc
  case excl_subclass hsc1 hss hs =>
    cases hsc
    case here hsub => cases hss.antisymm hsub
    case there hsc => apply hs.absurd_r hsc
  case excl_disjoint hd hss hs =>
    cases hsc
    case here hsub => cases hss.antisymm hsub
    case there hsc => apply hs.absurd_r hsc
  case excl_irrelevant hd hs =>
    cases hsc
    case here hsub => cases hd.symm.not_subclass hsub
    case there hsc => apply hs.absurd_r hsc

theorem Kind.Subkind.root_is_subclass (hs : Subkind (singleton r1 es1) (singleton r2 es2)) : HasSuperclassOf r1 es1 ∨ r1.Subclass r2 := by
  cases hs
  case absurd_l => left; assumption
  case subclass_no_excl => right; assumption
  case excl_subclass hsc hss hs =>
    cases hs.root_is_subclass <;> aesop
  case excl_disjoint hs =>
    cases hs.root_is_subclass <;> aesop
  case excl_irrelevant hs =>
    cases hs.root_is_subclass <;> aesop

theorem Kind.Subkind.refine_has_superclass
  (hs : Subkind (singleton r1 es1) (singleton r2 es2))
  (hsc : HasSuperclassOf a es2)
  : HasSuperclassOf r1 es1 ∨ r1.Disjoint a ∨ HasSuperclassOf a es1 := by
  cases hs
  case absurd_l => aesop
  case subclass_no_excl => cases hsc
  case excl_subclass hsc hss hs =>
    cases hsc
    case here hsub => have h := hsc.subclass hsub; aesop
    case there hsc => apply hs.refine_has_superclass hsc
  case excl_disjoint hd hss hs =>
    cases hsc
    case here hsub => have h:= (hd.refines_subclass_l hsub).symm; aesop
    case there hsc => apply hs.refine_has_superclass hsc
  case excl_irrelevant hd hs =>
    cases hsc
    case here hsub =>
      cases hs.root_is_subclass
      case inl => aesop
      case inr hsub2 => have h := ((hd.refines_subclass_l hsub).refines_subclass_r hsub2).symm; aesop
    case there hsc => apply hs.refine_has_superclass hsc

theorem Kind.Disjoint.refine_by_subkind
  (hd : Disjoint K2 L)
  (hs : Subkind K1 K2)
  : Disjoint K1 L := by
  induction hs generalizing L
  case absurd_l => apply! absurd_l
  case subclass_no_excl hsub =>
    cases hd
    case absurd_l hsc => cases hsc
    case absurd_r hsc => apply! absurd_r
    case root_l hsc => apply! root_l $ hsc.subclass _
    case root_r hsc =>  cases hsc
    case root hd => apply! root $ hd.refines_subclass_l _
  case excl_subclass hs hss hsc ih =>
    cases hd
    case absurd_l hsc =>
      cases hsc
      case here hsub => cases hss.antisymm hsub
      case there hsc => apply absurd_l $ hs.absurd_r hsc
    case absurd_r => apply! absurd_r
    case root_l hsc1 =>
      cases hs.root_is_subclass
      case inl => apply! absurd_l
      case inr hsub => apply! root_l $ hsc1.subclass _
    case root_r hsc1 =>
      cases hsc1
      case here hsub => apply! root_r $ hsc.subclass _
      case there hsc1 =>
        cases hs.refine_has_superclass hsc1
        case inl => apply! absurd_l
        case inr h1 =>
          cases h1
          case inl h1 => apply! root
          case inr h1 => apply! root_r
    case root hd =>
      cases hs.root_is_subclass
      case inl => apply! absurd_l
      case inr h1 => apply! root $ hd.refines_subclass_l _
  case excl_disjoint hs hss hd1 ih =>
    cases hd
    case absurd_l hsc =>
      cases hsc
      case here hsub => cases hss.antisymm hsub
      case there hsc => apply absurd_l $ hs.absurd_r hsc
    case absurd_r => apply! absurd_r
    case root_l hsc1 =>
      cases hs.root_is_subclass
      case inl => apply! absurd_l
      case inr hsub => apply! root_l $ hsc1.subclass _
    case root_r hsc1 =>
      cases hsc1
      case here hsub => apply! root $ hd1.symm.refines_subclass_r _
      case there hsc1 =>
        cases hs.refine_has_superclass hsc1
        case inl => apply! absurd_l
        case inr h1 =>
          cases h1
          case inl h1 => apply! root
          case inr h1 => apply! root_r
    case root hd2 =>
      cases hs.root_is_subclass
      case inl => apply! absurd_l
      case inr => apply! root $ hd2.refines_subclass_l _
  case excl_irrelevant hs hd ih =>
    cases hd
    case absurd_l hsc =>
      cases hsc
      case here hsub => cases hd.symm.not_subclass hsub
      case there hsc => apply absurd_l $ hs.absurd_r hsc
    case absurd_r => apply! absurd_r
    case root_l hsc1 =>
      cases hs.root_is_subclass
      case inl => apply! absurd_l
      case inr hsub => apply! root_l $ hsc1.subclass _
    case root_r hsc1 =>
      cases hsc1
      case here hsub =>
        cases hs.root_is_subclass
        case inl => apply! absurd_l
        case inr hsub2 =>
          apply root
          apply Classifier.Disjoint.symm
          apply! (hd.refines_subclass_l _).refines_subclass_r _
      case there hsc1 =>
        cases hs.refine_has_superclass hsc1
        case inl => apply! absurd_l
        case inr h1 =>
          cases h1
          case inl h1 => apply! root
          case inr h1 => apply! root_r
    case root hd2 =>
      cases hs.root_is_subclass
      case inl => apply! absurd_l
      case inr => apply! root $ hd2.refines_subclass_l _
