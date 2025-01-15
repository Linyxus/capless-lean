namespace Capybara

/-!

-/
inductive FiniteSet : Type -> Type where
| empty : FiniteSet A
| union : FiniteSet A -> FiniteSet A -> FiniteSet A
| singleton : A -> FiniteSet A

end Capybara
