import Capless.Classifier.Core
import Capless.Classifier.Kind
import Capless.Classifier.Intersection
import Capless.Classifier.Subtract
import Capless.Classifier.Subkind

namespace Capless

-- inductive Kind.Disjoint : Kind -> Kind -> Prop where
--   | empty_l: Disjoint .empty K
--   | empty_r : Disjoint K .empty
--   | union_l : Disjoint K1 K -> Disjoint K2 K -> Disjoint (K1.union K2) K
--   | union_r : Disjoint K K1 -> Disjoint K K2 -> Disjoint K (K1.union K2)
--   | absurd_l : ContainsSupOf ex1 r1 -> Disjoint (.node r1 ex1) (.node r2 ex2)
--   | absurd_r : ContainsSupOf ex2 r2 -> Disjoint (.node r1 ex1) (.node r2 ex2)
--   | root : r1.Disjoint r2 -> Disjoint (.node r1 ex1) (.node r2 ex2)
--   | excl_l : ContainsSupOf ex2 r1 -> Disjoint (.node r1 ex1) (.node r2 ex2)
--   | excl_r : ContainsSupOf ex1 r2 -> Disjoint (.node r1 ex1) (.node r2 ex2)

-- theorem Kind.Disjoint.union_l_inv (hd : Disjoint (K1.union K2) K) : Disjoint K1 K ∧ Disjoint K2 K := by
--   generalize hk : Kind.union K1 K2 = K' at hd
--   induction hd with
--   | empty_l => cases hk
--   | empty_r => exact ⟨.empty_r, .empty_r⟩
--   | union_l hd1 hd2 =>
--     cases hk
--     exact ⟨hd1, hd2⟩
--   | union_r hd1 hd2 ih1 ih2 =>
--     have ⟨hd1', hd2'⟩ := ih1 hk
--     have ⟨hd1'', hd2''⟩ := ih2 hk
--     exact ⟨.union_r hd1' hd1'', .union_r hd2' hd2''⟩
--   | absurd_l => cases hk
--   | absurd_r => cases hk
--   | root => cases hk
--   | excl_l => cases hk
--   | excl_r => cases hk

-- theorem Kind.Disjoint.union_r_inv (hd : Disjoint K (K1.union K2)) : Disjoint K K1 ∧ Disjoint K K2 := by
--   generalize hk : Kind.union K1 K2 = K' at hd
--   induction hd with
--   | empty_l => exact ⟨.empty_l, .empty_l⟩
--   | empty_r => cases hk
--   | union_l hd1 hd2 ih1 ih2 =>
--     have ⟨hd1', hd2'⟩ := ih1 hk
--     have ⟨hd1'', hd2''⟩ := ih2 hk
--     exact ⟨.union_l hd1' hd1'', .union_l hd2' hd2''⟩
--   | union_r hd1 hd2 =>
--     cases hk
--     exact ⟨hd1, hd2⟩
--   | absurd_l => cases hk
--   | absurd_r => cases hk
--   | root => cases hk
--   | excl_l => cases hk
--   | excl_r => cases hk

-- theorem Kind.Disjoint.implies_empty_intersect (hd : K1.Disjoint K2) (hi : Intersect K1 K2 R) : IsEmpty R := by
--   induction hi with
--   | empty_l => exact .empty
--   | empty_r => exact .empty
--   | union_l hi1 hi2 ih1 ih2 =>
--     have ⟨hd1, hd2⟩ := hd.union_l_inv
--     exact .union (ih1 hd1) (ih2 hd2)
--   | union_r hi1 hi2 ih1 ih2 =>
--     have ⟨hd1, hd2⟩ := hd.union_r_inv
--     exact .union (ih1 hd1) (ih2 hd2)
--   | singleton_l hs =>
--     cases hd with
--     | absurd_l ha => exact .absurd (.append_l ha)
--     | absurd_r ha => exact .absurd (.append_r (ha.trans_subclass hs))
--     | root hd => cases hd.not_subclass hs
--     | excl_l ha => exact .absurd (.append_r ha)
--     | excl_r ha => exact .absurd (.append_l (ha.trans_subclass hs))
--   | singleton_r hs =>
--     cases hd with
--     | absurd_l ha => exact .absurd (.append_l (ha.trans_subclass hs))
--     | absurd_r ha => exact .absurd (.append_r ha)
--     | root hd => cases hd.symm.not_subclass hs
--     | excl_l ha => exact .absurd (.append_r (ha.trans_subclass hs))
--     | excl_r ha => exact .absurd (.append_l ha)
--   | singleton_disj => exact .empty

-- theorem Kind.Disjoint.from_empty_intersect (hi : Intersect K1 K2 R) (he : IsEmpty R) : K1.Disjoint K2 := by
--   induction hi with
--   | empty_l => exact .empty_l
--   | empty_r => exact .empty_r
--   | union_l hi1 hi2 ih1 ih2 =>
--     cases he with
--     | union he1 he2 => exact .union_l (ih1 he1) (ih2 he2)
--   | union_r hi1 hi2 ih1 ih2 =>
--     cases he with
--     | union he1 he2 => exact .union_r (ih1 he1) (ih2 he2)
--   | singleton_l hs =>
--     cases he with
--     | absurd ha =>
--       cases ha.of_append with
--       | inl ha => exact .absurd_l ha
--       | inr ha => exact .excl_l ha
--   | singleton_r hs =>
--     cases he with
--     | absurd ha =>
--       cases ha.of_append with
--       | inl ha => exact .excl_r ha
--       | inr ha => exact .absurd_r ha
--   | singleton_disj hd => exact .root hd

-- theorem Kind.Disjoint.top_l (hd: Disjoint .top K) : IsEmpty K := by
--   cases hd
--   case empty_r => constructor
--   case union_r ha hb => apply IsEmpty.union ha.top_l hb.top_l
--   case absurd_l hsc => cases hsc
--   case absurd_r hsc => constructor; assumption
--   case root hd => cases hd.symm.not_subclass .of_top
--   case excl_l hsc => constructor; apply hsc.trans_subclass .of_top
--   case excl_r hsc => cases hsc

-- theorem Kind.Disjoint.symm (hd : K1.Disjoint K2) : Disjoint K2 K1 := by
--   induction hd with
--   | empty_l => exact .empty_r
--   | empty_r => exact .empty_l
--   | union_l _ _ ih1 ih2 => exact .union_r ih1 ih2
--   | union_r _ _ ih1 ih2 => exact .union_l ih1 ih2
--   | absurd_l ha => exact .absurd_r ha
--   | absurd_r ha => exact .absurd_l ha
--   | root hd => exact .root hd.symm
--   | excl_l ha => exact .excl_r ha
--   | excl_r ha => exact .excl_l ha

-- theorem Kind.Disjoint.append_excl_l (hd : Disjoint (.node r1 ex2) K) : Disjoint (.node r1 (ex1 ++ ex2)) K := by
--   cases hd
--   case empty_r => apply! empty_r
--   case union_r ha hb => apply union_r ha.append_excl_l hb.append_excl_l
--   case absurd_l ha => apply absurd_l ha.append_r
--   case absurd_r => apply! absurd_r
--   case root => apply! root
--   case excl_l => apply! excl_l
--   case excl_r ha => apply excl_r ha.append_r

-- theorem Kind.Disjoint.refine_subroot_l (hd : Disjoint (.node r1 ex1) K) (hs : r2.Subclass r1) : Disjoint (.node r2 ex1) K := by
--   cases hd
--   case empty_r => apply! empty_r
--   case union_r ha hb => apply! union_r (ha.refine_subroot_l _) (hb.refine_subroot_l _)
--   case absurd_l ha => apply! absurd_l $ ha.trans_subclass _
--   case absurd_r => apply! absurd_r
--   case root hdr => apply root; apply! hdr.refines_subclass_l _
--   case excl_l hc => apply! excl_l $ hc.trans_subclass _
--   case excl_r => apply! excl_r

-- -- If K1 is disjoint from K', and R is the intersection of K with K1, then R is disjoint from K'
-- theorem Kind.Disjoint.intersect_disjoint (hd : K1.Disjoint K') (hi : Intersect K K1 R) : R.Disjoint K' := by
--   induction hi
--   case empty_l => apply! empty_l
--   case empty_r => apply! empty_l
--   case union_l iha ihb => apply! union_l (iha _) (ihb _)
--   case union_r iha ihb =>
--     have ⟨_, _⟩ := hd.union_l_inv
--     apply! union_l (iha _) (ihb _)
--   case singleton_l hs => apply append_excl_l; apply! hd.refine_subroot_l _
--   case singleton_r hs => apply hd.append_excl_l
--   case singleton_disj hdr => apply empty_l

-- theorem Kind.Disjoint.absurd_l' (hs : ContainsSupOf ex1 r1) : Disjoint (.node r1 ex1) K := by
--   induction K
--   case empty => apply empty_r
--   case node => apply! absurd_l
--   case union ha hb => apply! union_r

-- theorem Kind.Disjoint.refine_subtract_l (hd : Disjoint K1 K) (hs : Subtract K1 K2 R) : Disjoint R K := by
--   induction hs
--   case empty_l => exact .empty_l
--   case union_l ih1 ih2 =>
--     have ⟨hd1, hd2⟩ := hd.union_l_inv
--     exact .union_l (ih1 hd1) (ih2 hd2)
--   case empty_r => assumption
--   case union_r ih1 ih2 => exact ih2 (ih1 hd)
--   case tree => apply! hd.append_excl_l (ex1 := [_])
--   case excl_absurd_r => assumption
--   case excl_irrelevant_r ih => apply! ih
--   case excl_subclass_r hs1 _ ih =>
--     apply Disjoint.union_l
--     apply! ih
--     apply! hd.refine_subroot_l
--   case excl_subclass_l => assumption
--   case excl_irrelevant_l ih => apply! ih

-- theorem Kind.Disjoint.append_l_disj_inv (hd : Disjoint (.node r1 (a :: ex1)) (.node r2 ex2)) (hda : a.Disjoint r2) : Disjoint (.node r1 ex1) (.node r2 ex2) := by
--   cases hd
--   case absurd_l hsc =>
--     cases hsc
--     case here hs => apply! root $ hda.refines_subclass_l _
--     case there hsc => apply! absurd_l
--   case absurd_r => apply! absurd_r
--   case root => apply! root
--   case excl_l hsc => apply! excl_l
--   case excl_r hsc =>
--     cases hsc
--     case here hs => cases hda.symm.not_subclass hs
--     case there => apply! excl_r

-- theorem Kind.Disjoint.append_l_contained_inv (hd : Disjoint (.node r1 (a :: ex1)) (.node r2 ex2)) (hsc: ContainsSupOf ex2 a) : Disjoint (.node r1 ex1) (.node r2 ex2) := by
--   cases hd
--   case absurd_l hsc =>
--     cases hsc
--     case here hs => apply! excl_l $ hsc.trans_subclass _
--     case there hsc => apply! absurd_l
--   case absurd_r => apply! absurd_r
--   case root => apply! root
--   case excl_l hsc => apply! excl_l
--   case excl_r hsc =>
--     cases hsc
--     case here hs => apply! absurd_r $ hsc.trans_subclass _
--     case there => apply! excl_r

-- theorem Kind.Disjoint.refine_disjoint_subtract_l_disjoint_root
--   (hdr : Disjoint R K)
--   (hs : Subtract (.node r1 ex1) (.node r2 ex2) R)
--   (hd : r1.Disjoint r2)
--   : Disjoint (.node r1 ex1) K := by
--   cases hs
--   case tree =>
--     generalize h : node r1 (r2 :: ex1) = L at hdr
--     induction hdr <;> try cases h
--     case empty_r => apply! empty_r
--     case union_r ha hb => simp_all; apply! union_r
--     case absurd_l hsc =>
--       cases hsc
--       case here hs => cases hd.not_subclass hs
--       case there hsc => apply! absurd_l
--     case absurd_r => apply! absurd_r
--     case root hd2 => apply! root
--     case excl_l => apply! excl_l
--     case excl_r hsc =>
--       cases hsc
--       case here hs => apply! root $ hd.refines_subclass_r _
--       case there hsc => apply! excl_r
--   case excl_absurd_r => assumption
--   case excl_irrelevant_r hs => apply! hdr.refine_disjoint_subtract_l_disjoint_root
--   case excl_subclass_r hs =>
--     have ⟨hl, _⟩ := hdr.union_l_inv
--     apply! hl.refine_disjoint_subtract_l_disjoint_root _ hd
--   case excl_subclass_l => assumption
--   case excl_irrelevant_l hs => apply! hdr.refine_disjoint_subtract_l_disjoint_root

-- theorem Kind.Disjoint.refine_disjoint_subtract_l_subroot
--   (hdr : Disjoint R K)
--   (hs : Subtract (.node r1 ex1) (.node r2 ex2) R)
--   (hsub : r2.Subclass r1)
--   (hd2 : Disjoint (.node r2 ex1) K)
--   : Disjoint (.node r1 ex1) K := by
--   cases hs
--   case tree =>
--     generalize h : node r1 (r2 :: ex1) = L at hdr
--     induction hdr <;> try cases h
--     case empty_r => apply! empty_r
--     case union_r ha hb =>
--       have ⟨_, _⟩ := hd2.union_r_inv
--       simp_all
--       apply! union_r
--     case absurd_l hsc =>
--       cases hsc
--       case here hs2 => cases hsub.antisymm hs2; assumption
--       case there => apply! absurd_l
--     case absurd_r => apply! absurd_r
--     case root => apply! root
--     case excl_l => apply! excl_l
--     case excl_r hsc =>
--       cases hsc
--       case here hs2 =>
--         cases hd2
--         case absurd_l => apply excl_r; apply! ContainsSupOf.trans_subclass
--         case absurd_r => apply! absurd_r
--         case root hd => cases hd.symm.not_subclass hs2
--         case excl_l hsc => apply! absurd_r $ hsc.trans_subclass _
--         case excl_r hsc => apply! excl_r
--       case there hsc => apply! excl_r
--   case excl_absurd_r => assumption
--   case excl_irrelevant_r hs =>  apply! hdr.refine_disjoint_subtract_l_subroot
--   case excl_subclass_r hs =>
--     have ⟨hl, _⟩ := hdr.union_l_inv
--     apply! hl.refine_disjoint_subtract_l_subroot
--   case excl_subclass_l => assumption
--   case excl_irrelevant_l hs => apply! hdr.refine_disjoint_subtract_l_subroot



-- theorem Kind.Disjoint.refine_disjoint_subtract_l (hd2 : Disjoint K2 K) (hs : Subtract K1 K2 R) (hdr : Disjoint R K) : Disjoint K1 K := by
--   induction hs generalizing K
--   case empty_l => apply empty_l
--   case union_l ih1 ih2 =>
--     have ⟨_, _⟩ := hdr.union_l_inv
--     apply! union_l (ih1 _ _) (ih2 _ _)
--   case empty_r => assumption
--   case union_r ha hb =>
--     have ⟨hl, hr⟩ := hd2.union_l_inv
--     apply ha hl _
--     apply hb hr hdr
--   case tree r1 ex1 r2 =>
--     generalize h : node r1 (r2 :: ex1) = L at hdr
--     induction hdr <;> try cases h
--     case empty_r => apply! empty_r
--     case union_r ha hb =>
--       have ⟨_, _⟩ := hd2.union_r_inv
--       simp_all
--       apply! union_r
--     case absurd_l hsc =>
--       cases hsc
--       case here hs =>
--         cases hd2
--         case absurd_l hsc => cases hsc
--         case absurd_r hsc => apply! absurd_r
--         case root hd =>  apply root; apply! hd.refines_subclass_l _
--         case excl_l hsc => apply excl_l; apply! hsc.trans_subclass
--         case excl_r hsc => cases hsc
--       case there hsc => apply! absurd_l
--     case absurd_r => apply! absurd_r
--     case root => apply! root
--     case excl_l => apply! excl_l
--     case excl_r hsc =>
--       cases hsc
--       case here hs =>
--         cases hd2
--         case absurd_r hsc => apply! absurd_r
--         case root hd => cases hd.symm.not_subclass hs
--         case excl_l hsc => apply absurd_r; apply! hsc.trans_subclass
--         case excl_r hsc => cases hsc
--         case absurd_l hsc => cases hsc
--       case there hsc => apply! excl_r
--   case excl_subclass_r r1 ex1 r2 ex2 _ a hss hsc hs ih =>
--     have ⟨hdr1, hdr2⟩ := hdr.union_l_inv
--     generalize h : node r2 (a :: ex2) = L at hd2
--     induction hd2 generalizing K2 <;> try cases h
--     case empty_r => apply! empty_r
--     case union_r ha hb =>
--       simp_all
--       have ⟨_, _⟩ := hdr.union_r_inv
--       have ⟨_, _⟩ := hdr1.union_r_inv
--       have ⟨_, _⟩ := hdr2.union_r_inv
--       apply! union_r (ha _ _ _) (hb _ _ _)
--     case absurd_l hsc =>
--       cases hsc
--       case here hsc1 =>
--         cases hss.antisymm hsc1
--         apply! hdr1.refine_disjoint_subtract_l_subroot
--       case there hsc =>
--         apply ih _ hdr1
--         apply! absurd_l
--     case absurd_r => apply! absurd_r
--     case root hd1 => apply ih (.root hd1) hdr1
--     case excl_l hsc => apply! ih (.excl_l _)
--     case excl_r hsc =>
--       cases hsc
--       case here hs =>
--         cases hdr2
--         case absurd_l hsc => apply! excl_r $ hsc.trans_subclass _
--         case absurd_r => apply! absurd_r
--         case root hd => cases hd.symm.not_subclass hs
--         case excl_l hsc => apply! absurd_r $ hsc.trans_subclass _
--         case excl_r => apply! excl_r
--       case there hsc => apply! ih (excl_r _)
--   case excl_absurd_r hs => assumption
--   case excl_irrelevant_r r1 ex1 r2 ex2 _ a hd hs ih =>
--     generalize h : node r2 (a :: ex2) = L at hd2
--     induction hd2 generalizing K2 <;> try cases h
--     case empty_r => apply! empty_r
--     case union_r ha hb =>
--       simp_all
--       have ⟨_, _⟩ := hdr.union_r_inv
--       apply! union_r (ha _) (hb _)
--     case absurd_l hsc =>
--       cases hsc
--       case here hsc => cases hd.not_subclass hsc
--       case there hsc =>
--         apply ih _ hdr
--         apply! absurd_l
--     case absurd_r => apply! absurd_r
--     case root hd1 => apply ih (.root hd1) hdr
--     case excl_l hsc => apply! ih (.excl_l _)
--     case excl_r hsc =>
--       cases hsc
--       case here hs => apply ih _ hdr; apply root; apply! hd.refines_subclass_r
--       case there hsc => apply! ih (excl_r _)
--   case excl_subclass_l hs2 hs1 => assumption
--   case excl_irrelevant_l r1 ex1 r2 ex2 _ a hs2 hd1 hs ih =>
--     generalize h : node r2 (a :: ex2) = L at hd2
--     induction hd2 generalizing K2 <;> try cases h
--     case empty_r => apply! empty_r
--     case union_r ha hb =>
--       simp_all
--       have ⟨_, _⟩ := hdr.union_r_inv
--       apply! union_r (ha _) (hb _)
--     case absurd_l hsc =>
--       cases hsc
--       case here hsc =>
--         cases hs2.antisymm hsc
--         apply! hdr.refine_disjoint_subtract_l_disjoint_root hs
--       case there hsc =>
--         apply ih _ hdr
--         apply! absurd_l
--     case absurd_r => apply! absurd_r
--     case root hd1 => apply ih (.root hd1) hdr
--     case excl_l hsc => apply! ih (.excl_l _)
--     case excl_r hsc =>
--       cases hsc
--       case here hs => apply root; apply! hd1.refines_subclass_r
--       case there hsc => apply! ih (excl_r _)

-- theorem Kind.Disjoint.is_empty_l (he : IsEmpty K) : Disjoint K L := by
--   induction he
--   case empty => apply empty_l
--   case absurd => apply! absurd_l'
--   case union ha hb => apply! union_l

-- theorem Kind.Disjoint.refine_subkind_l' (hd : Disjoint K2 K) (hs : Subtract K1 K2 R) (he : IsEmpty R) : Disjoint K1 K := by
--   apply refine_disjoint_subtract_l hd hs
--   apply is_empty_l he

-- theorem Kind.Disjoint.refine_subkind_l (hd : Disjoint K2 K) (hs : Subkind K1 K2) : Disjoint K1 K := by
--   cases hs
--   apply! hd.refine_subkind_l'

-- theorem Kind.Subkind.refine_disjoint_l (hs : Subkind K1 K2) (hd : Disjoint K2 K) : Disjoint K1 K := hd.refine_subkind_l hs


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

@[simp]
def Kind.contains_sup_of (exs : List Classifier) (c : Classifier) :=
  match exs with
  | .nil => false
  | .cons head tail => c.subclass head || contains_sup_of tail c

theorem Kind.ContainsSupOf.lawful : ContainsSupOf exs r ↔ contains_sup_of exs r := by
  apply Iff.intro
  . intro hsc
    induction hsc
    case here hs => simp; simp_all [Classifier.subclass_is_Subclass]
    case there ih => simp_all
  . intro hsc
    unfold contains_sup_of at hsc
    split at hsc
    . aesop
    . simp at hsc
      cases hsc <;> rename_i hsc
      . apply ContainsSupOf.here; simp_all [Classifier.subclass_is_Subclass]
      . apply ContainsSupOf.there; rw [← lawful] at hsc; simp_all

-- @[simp]
-- def Kind.disjoint (K1 : Kind) (K2 : Kind) :=
--   match K1 with
--   | .empty => true
--   | .union a b => a.disjoint K2 && b.disjoint K2
--   | .node r1 ex1 =>
--     match K2 with
--     | .empty => true
--     | .union a b => (Kind.node r1 ex1).disjoint a && (Kind.node r1 ex1).disjoint b
--     | .node r2 ex2 =>
--       r1.disjoint r2
--         || contains_sup_of ex1 r1 || contains_sup_of ex2 r2
--         || contains_sup_of ex1 r2 || contains_sup_of ex2 r1

-- theorem Kind.Disjoint.lawful : Disjoint K1 K2 ↔ K1.disjoint K2 := by
--   apply Iff.intro
--   . intro hd
--     induction hd
--     case empty_l => simp
--     case empty_r K =>
--       induction K <;> simp_all
--     case union_l => simp_all
--     case union_r K K1 K2 _ _ ha hb =>
--       induction K <;> simp_all
--       rename_i iha ihb hha hhb
--       have ⟨_, _⟩ := hha.union_l_inv
--       have ⟨_, _⟩ := hhb.union_l_inv
--       apply And.intro
--       apply! iha
--       apply! ihb
--     case absurd_l hsc => simp_all [ContainsSupOf.lawful]
--     case absurd_r hsc => simp_all [ContainsSupOf.lawful]
--     case root hd => simp_all [Classifier.disjoint_is_Disjoint]
--     case excl_l => simp_all [ContainsSupOf.lawful]
--     case excl_r => simp_all [ContainsSupOf.lawful]
--   . intro hd
--     induction K1
--     case empty => apply empty_l
--     case union ha hb =>
--       apply union_l <;> simp_all
--     case node r1 ex1 =>
--       induction K2
--       case empty => apply empty_r
--       case union ha hb =>
--         apply union_r <;> simp_all
--       case node r2 ex2 =>
--         simp at hd; rw [← Classifier.disjoint_is_Disjoint] at hd; repeat rw [← ContainsSupOf.lawful] at hd
--         cases hd <;> rename_i hd
--         . cases hd <;> rename_i hd
--           . cases hd <;> rename_i hd
--             . cases hd <;> rename_i hd
--               . apply! root
--               . apply! absurd_l
--             . apply! absurd_r
--           . apply! excl_r
--         . apply! excl_l


-- inductive Kind.Contains : Kind -> Classifier -> Prop where
--   | union_l : Contains K1 c -> Contains (.union K1 K2) c
--   | union_r : Contains K2 c -> Contains (.union K1 K2) c
--   | subclass : Classifier.Subclass c r -> Contains (.node r []) c
--   | excl_sub :
--     Classifier.StrictSub a c ->
--     Contains (.node r exs) c ->
--     Contains (.node r (a :: exs)) c
--   | excl_irrelevant :
--     Classifier.Disjoint a c ->
--     Contains (.node r exs) c ->
--     Contains (.node r (a :: exs)) c

-- theorem Kind.Contains.is_subclass
--   (hc : Contains (.node r exs) c)
--   : c.Subclass r := by
--   cases hc
--   case subclass => assumption
--   case excl_sub hc => apply hc.is_subclass
--   case excl_irrelevant hc => apply hc.is_subclass

-- theorem Kind.Contains.not_empty
--   (hc : Contains K c)
--   (he : IsEmpty K)
--   : False := by
--   induction he
--   case empty => cases hc
--   case absurd exs r hsc =>
--     induction hsc
--     case here hs =>
--       cases hc
--       case excl_sub hss hc =>
--         apply hss.antisymm
--         apply hc.is_subclass.trans hs
--       case excl_irrelevant hd hc =>
--         apply hd.symm.not_subclass
--         apply hc.is_subclass.trans hs
--     case there hsc ih =>
--       cases hc <;> apply! ih
--   case union ha hb =>
--     cases hc
--     apply! ha
--     apply! hb

-- theorem Kind.Contains.excl_irrelevant_l
--   (hd : Classifier.Disjoint r a)
--   (hc : Contains (.node r exs) c)
--   : Contains (.node r (a :: exs)) c := by
--   cases c.subclass_or_disjoint a <;> rename_i hs
--   . cases (hd.refines_subclass_l hc.is_subclass).not_subclass hs
--   . cases hs <;> rename_i hs
--     . apply! excl_sub
--     . apply! excl_irrelevant hs.symm

-- theorem Kind.Contains.change_root
--   (hc : Contains (.node r exs) c)
--   (hs1 : c.Subclass a)
--   : Contains (.node a exs) c := by
--   cases hc
--   case subclass => apply! subclass
--   case excl_sub hss hc => apply excl_sub hss; apply! hc.change_root
--   case excl_irrelevant hd hc => apply excl_irrelevant hd; apply! hc.change_root

-- theorem Kind.Contains.excl_append
--   (hc1 : Contains (.node r ex1) c)
--   (hc2 : Contains (.node r ex2) c)
--   : Contains (.node r (ex1 ++ ex2)) c := by
--   induction ex1
--   case nil => exact hc2
--   case cons head tail ih =>
--     cases hc1
--     case excl_sub => apply! excl_sub _ (ih _)
--     case excl_irrelevant => apply! excl_irrelevant _ (ih _)

-- theorem Kind.Contains.subtract
--   (hc : Contains K c)
--   (hs : Subtract K L R)
--   : Contains L c ∨ Contains R c := by
--   induction hs
--   case empty_l => cases hc.not_empty .empty
--   case union_l ha hb =>
--     cases hc <;> rename_i hc
--     . cases ha hc
--       . aesop
--       . right; apply union_l; assumption
--     . cases hb hc
--       . aesop
--       . right; apply union_r; assumption
--   case empty_r => aesop
--   case union_r ha hb =>
--     cases ha hc <;> rename_i ha
--     . left; apply union_l; assumption
--     . cases hb ha <;> rename_i hb
--       . left; apply union_r; assumption
--       . aesop
--   case tree r1 _ r2 =>
--     cases c.subclass_or_disjoint r2 <;> rename_i hs
--     . left; constructor; assumption
--     . cases hs <;> rename_i hs
--       . right; apply! excl_sub
--       . right; apply excl_irrelevant hs.symm hc
--   case excl_absurd_r hss => aesop
--   case excl_irrelevant_r hd _ ih =>
--     cases ih hc
--     case inl hc => left; apply! excl_irrelevant_l
--     case inr => aesop
--   case excl_subclass_r a hs2 hs1 _ ih =>
--     cases ih hc <;> rename_i ih
--     . cases c.subclass_or_disjoint a <;> rename_i hs
--       . right; apply union_r; apply! change_root
--       . cases hs <;> rename_i hs
--         . left; apply! excl_sub
--         . left; apply! excl_irrelevant (.symm _)
--     . right; apply! union_l
--   case excl_subclass_l hs2 hss => aesop
--   case excl_irrelevant_l hs2 hd1 _ ih =>
--     cases ih hc <;> rename_i ih
--     . left; apply excl_irrelevant _ ih; apply hd1.symm.refines_subclass_r hc.is_subclass
--     . aesop

-- theorem Kind.Contains.refine_subkind
--   (hc : Contains K c)
--   (hs : Subkind K L)
--   : Contains L c := by
--   cases hs
--   rename_i hs he
--   cases hc.subtract hs
--   . assumption
--   . rename_i hc; cases hc.not_empty he

-- theorem Kind.Contains.intersect'
--   (hc1 : Contains K1 c)
--   (hc2: Contains K2 c)
--   (hi : Intersect K1 K2 R)
--   : Contains R c := by
--   induction hi
--   case empty_l => cases hc1.not_empty .empty
--   case empty_r => cases hc2.not_empty .empty
--   case union_l ha hb =>
--     simp_all
--     cases hc1
--     . apply! union_l (ha _)
--     . apply! union_r (hb _)
--   case union_r ha hb =>
--     simp_all
--     cases hc2
--     . apply! union_l (ha _)
--     . apply! union_r (hb _)
--   case singleton_l =>
--     apply excl_append hc1 (hc2.change_root hc1.is_subclass)
--   case singleton_r =>
--     apply excl_append (hc1.change_root hc2.is_subclass) hc2
--   case singleton_disj hd =>
--     cases (hd.refines_subclass_l hc1.is_subclass).not_subclass hc2.is_subclass

-- theorem Kind.Contains.intersect
--   (hc1 : Contains K1 c)
--   (hc2 : Contains K2 c)
--   : Contains (K1.intersect K2) c := intersect' hc1 hc2 (Intersect.lawful)

-- @[simp]
-- def Kind.contains (K : Kind) (c : Classifier) : Bool :=
--   match K with
--   | .empty => false
--   | .union K1 K2 => K1.contains c || K2.contains c
--   | .node r exs =>
--     match exs with
--     | .nil => c.subclass r
--     | .cons a xs =>
--       if a.subclass c && a != c then (Kind.node r xs).contains c
--       else if a.disjoint c then (Kind.node r xs).contains c
--       else false

-- theorem Kind.Contains.lawful : Contains K c ↔ K.contains c := by
--   apply Iff.intro
--   . intro hc
--     induction hc <;> try simp_all
--     case subclass hs => rw [← Classifier.subclass_is_Subclass]; assumption
--     case excl_sub hss _ _ => left; apply And.intro; rw [← Classifier.subclass_is_Subclass]; apply hss.weaken; apply hss.neq
--     case excl_irrelevant hd _ _ => right; rw [← Classifier.disjoint_is_Disjoint]; assumption
--   . intro hc
--     unfold contains at hc
--     split at hc
--     . aesop
--     . simp at hc; cases hc
--       . apply union_l; rw [lawful]; assumption
--       . apply union_r; rw [lawful]; assumption
--     . split at hc
--       . constructor; rw [Classifier.subclass_is_Subclass]; assumption
--       . simp at hc
--         split at hc
--         . rename_i h
--           have ⟨h1, h2⟩ := h
--           apply excl_sub
--           rw [← Classifier.subclass_is_Subclass] at h1
--           cases h1.might_strict <;> aesop
--           rw [← lawful] at hc; aesop
--         . have ⟨h1, h2⟩ := hc
--           rw [← lawful] at h2
--           rw [← Classifier.disjoint_is_Disjoint] at h1
--           apply! excl_irrelevant

  -- : Contains (K1.intersect K2) c := by
  -- induction K1 generalizing K2
  -- case empty => cases hc1.not_empty .empty
  -- case union ha hb =>
  --   simp
  --   cases hc1
  --   apply! union_l (ha _ hc2)
  --   apply! union_r (hb _ hc2)
  -- case node r1 ex1 =>
