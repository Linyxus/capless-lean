import Capybara.StaticSemantics.CaptureRoot
namespace Capybara

/-!
`Γ ⊢ C1 >> C2` means that the effects of `C1` and `C2` are chainable.

Specifically, anything that has been dropped from `C1` cannot be mentioned by `C2` any more.
-/
def CaptureSet.Chaining (Γ : Context n m k) (C1 C2 : CaptureSet n k) : Prop :=
  ∀c, ReachRoot Γ C1 ⟨drop,c⟩ -> ∀m, ReachRoot Γ C2 ⟨m,c⟩ -> False

notation:50 Γ " ⊢ " C1 " >> " C2 => CaptureSet.Chaining Γ C1 C2

end Capybara
