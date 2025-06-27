import Capless.Term

/-!
# Value Preservation Under Weakening

This file proves that the `IsValue` property of terms is preserved under various weakening
operations. These theorems ensure that if a term is a value before weakening, it remains
a value after weakening the context.

The file provides preservation theorems for:
- `Term.IsValue.weaken`: Regular variable weakening
- `Term.IsValue.tweaken`: Type variable weakening
- `Term.IsValue.cweaken`: Capture variable weakening

These results are crucial for maintaining the structural properties of values throughout
type-preserving transformations.
-/

namespace Capless

theorem Term.IsValue.weaken
  (hv : Term.IsValue t) :
  Term.IsValue t.weaken := by
  cases hv <;> simp [Term.weaken, Term.rename] <;> constructor

theorem Term.IsValue.tweaken
  (hv : Term.IsValue t) :
  Term.IsValue t.tweaken := by
  cases hv <;> simp [Term.tweaken, Term.rename] <;> constructor

theorem Term.IsValue.cweaken
  (hv : Term.IsValue t) :
  Term.IsValue t.cweaken := by
  cases hv <;> simp [Term.cweaken, Term.rename] <;> constructor

end Capless
