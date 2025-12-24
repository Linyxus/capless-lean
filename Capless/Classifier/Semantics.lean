import Capless.Classifier.Subtract

namespace Capless

inductive Subtree.Contains : Subtree -> Classifier -> Prop where
  | sub : a.Subclass r -> Contains (mk r []) a
  | incl : ¬ a.Subclass x -> Contains (mk r exs) a -> Contains (mk r (x :: exs)) a

instance Subtree.Contains.decidable : Decidable (Contains (mk r exs) c) := by
  cases exs
  case nil =>
    cases Classifier.Subclass.decidable c r
    case isTrue h => apply! isTrue (.sub h)
    case isFalse h =>
      apply isFalse; intro h0; cases h0; simp_all
  case cons x xs =>
    cases decidable (r:=r) (exs:=xs) (c:=c)
    case isFalse => apply isFalse; intro h0; cases h0; simp_all
    case isTrue ih =>
      cases Classifier.Subclass.decidable c x
      case isFalse h => apply! (isTrue $ .incl h ih)
      case isTrue h => apply isFalse; intro h0; cases h0; simp_all

theorem Subtree.Contains.subclass_of_root (hc : Contains a c) : c.Subclass a.root := by
  induction hc
  case sub => assumption
  case incl ih => apply! ih

theorem Subtree.Contains.implies_root (hc : Contains a c) : Contains a a.root := by
  induction hc
  case sub => apply sub .rfl
  case incl r exs c x hns hc ih =>
    cases r.subclass_or_disjoint x <;> rename_i hx
    . cases c.subclass_or_disjoint x <;> rename_i hxc; aesop
      cases hxc <;> rename_i hxc
      . cases (hxc.subclass_l hx).antisymm hc.subclass_of_root
      . cases (hxc.refines_subclass_r hx).not_subclass hc.subclass_of_root
    . cases hx <;> rename_i hx
      . apply incl hx.antisymm ih
      . apply incl hx.not_subclass ih

inductive Kind.Contains : Kind -> Classifier -> Prop where
  | here : t.Contains x -> Contains (t :: ts) x
  | there : Contains ts x -> Contains (t :: ts) x

instance Kind.Contains.decidable : Decidable (Contains k c) := by
  cases k
  case nil => apply isFalse; intro h; cases h
  case cons x xs =>
    cases Subtree.Contains.decidable (r:=x.root) (exs:=x.excls) (c:=c)
    case isTrue h => apply! isTrue (.here h)
    case isFalse hNotHere =>
      cases decidable (k:=xs) (c:=c)
      case isTrue h => apply! isTrue (.there h)
      case isFalse hNotThere =>
        apply isFalse; intro h; cases h <;> aesop

-- Semantic empty
@[simp]
def Subtree.SEmpty (s : Subtree) : Prop := ∀ x, ¬ s.Contains x

@[simp]
def Kind.SEmpty (k : Kind) : Prop := ∀ x, ¬ k.Contains x

theorem Kind.SEmpty.cons_inv (hs : SEmpty (x :: xs)) : x.SEmpty ∧ SEmpty xs := by
  apply And.intro
  . intro c h
    apply hs c (.here h)
  . intro c h
    apply hs c (.there h)

theorem Subtree.SEmpty.excl_inv (he : SEmpty (mk r (x :: xs))) : r.Subclass x ∨ SEmpty (mk r xs) := by
  cases r.subclass_or_disjoint x; aesop
  rename_i h; cases h <;> rename_i h
  . right; intro _ h1; rename_i c
    apply he r $ .incl h.antisymm h1.implies_root
  . right; intro _ h1; rename_i c
    apply he r $ .incl h.not_subclass h1.implies_root

theorem Subtree.SEmpty.is_empty : (mk r exs).SEmpty ↔ ContainsSupOf exs r := by
  apply Iff.intro <;> intro h
  . induction exs
    case nil =>
      cases h r (.sub .rfl)
    case cons x xs ih =>
      cases h.excl_inv <;> rename_i h
      . apply! ContainsSupOf.here
      . apply! ContainsSupOf.there $ ih _
  . intro c h0
    induction h generalizing c
    case here hs => cases h0.implies_root; contradiction
    case there hsc ih => cases h0.implies_root; apply! ih

theorem Kind.SEmpty.is_empty : SEmpty k ↔ IsEmpty k := by
  apply Iff.intro <;> intro h
  . induction k
    case nil => constructor
    case cons x xs ih =>
      have ⟨h1, h2⟩ := h.cons_inv
      constructor
      . rw [← Subtree.SEmpty.is_empty]; exact h1
      . aesop
  . intro c hc
    induction h
    case empty => cases hc
    case absurd hsc h ih =>
      rw [← Subtree.SEmpty.is_empty] at hsc
      cases hc
      case here hc => apply hsc _ hc
      case there => apply! ih

theorem Subtree.Subtract.contains_or
  (hs : Subtract a b R1)
  (hca : a.Contains c)
  : b.Contains c ∨ R1.Contains c := by
  induction hs
  case tree r1 ex1 r2 =>
    cases Decidable.em (c.Subclass r2)
    . left; apply! Contains.sub
    . right; apply! Kind.Contains.here $ Contains.incl _ _
  case excl_absurd_r hss => right; apply! Kind.Contains.here
  case excl_irrelevant_r hd hs ih =>
    cases ih hca <;> rename_i ih
    . left; apply Contains.incl; apply (hd.refines_subclass_l ih.subclass_of_root).not_subclass; assumption
    . aesop
  case excl_subclass_r hsa2 hsa1 hs ih =>
    cases ih hca
    .


end Capless
