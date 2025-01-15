namespace Capybara

/-!
Inductively defined finite sets.
!-/
inductive FiniteSet : Type -> Type where
| empty : FiniteSet A
| union : FiniteSet A -> FiniteSet A -> FiniteSet A
| singleton : A -> FiniteSet A

/-!
Instances for finite sets: empty collection, union, singleton.
!-/
@[simp]
instance : EmptyCollection (FiniteSet A) where
  emptyCollection := FiniteSet.empty

@[simp]
instance : Union (FiniteSet A) where
  union := FiniteSet.union

@[simp]
instance : Singleton A (FiniteSet A) where
  singleton := FiniteSet.singleton

/-!
Definition of the renaming operator.
!-/
def FiniteSet.rename : FiniteSet A -> (A -> B) -> FiniteSet B
| FiniteSet.empty, _ => {}
| FiniteSet.union s1 s2, f => (s1.rename f) ∪ (s2.rename f)
| FiniteSet.singleton a, f => {f a}

/-!
Membership.
!-/
inductive FiniteSet.HasElem : FiniteSet A -> A -> Prop where
| singleton : FiniteSet.HasElem {a} a
| union_l : FiniteSet.HasElem s1 a -> FiniteSet.HasElem (s1 ∪ s2) a
| union_r : FiniteSet.HasElem s2 a -> FiniteSet.HasElem (s1 ∪ s2) a

instance : Membership (FiniteSet A) A where
  mem := fun a A => FiniteSet.HasElem A a

/-!
Properties of finite sets.
!-/
theorem FiniteSet.rename_empty : FiniteSet.rename {} f = {} := rfl

theorem FiniteSet.rename_singleton : FiniteSet.rename {a} f = {f a} := rfl

theorem FiniteSet.rename_union :
  FiniteSet.rename (s1 ∪ s2) f = (s1.rename f) ∪ (s2.rename f) :=
  rfl

end Capybara
