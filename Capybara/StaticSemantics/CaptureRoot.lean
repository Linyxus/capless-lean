import Capybara.Syntax
namespace Capybara

/-!
A capture root is a qualified access to an abstract capture variable.
-/
structure Root (k : Nat) where
  c : Fin k
  m : Mode

inductive Roots (k : Nat) where
| empty : Roots k
| cons : Root k -> Roots k -> Roots k

end Capybara
