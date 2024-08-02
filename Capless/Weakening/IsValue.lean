import Capless.Term
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
