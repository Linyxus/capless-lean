import Capybara.Syntax.Type
namespace Capybara

/-!
An indexed context. A `Context n m k` contains `n` term variables,
`m` type variables, and `k` capture set variables.
!-/
inductive Context : Nat -> Nat -> Nat -> Type where
| empty : Context 0 0 0
| cons : Context n m k -> CType n m k -> Context (n+1) m k
| tcons : Context n m k -> SType n m k -> Context n (m+1) k
| ccons : Context n m k -> CaptureSet n k -> Context n m (k+1)

end Capybara
