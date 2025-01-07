import Capybara.StaticSemantics.CaptureRoot
namespace Capybara

def CaptureRoot.Chaining (D1 D2 : CaptureRoot k) : Prop :=
  ∀c, HasElem D1 c drop -> (∀m, HasElem D2 c m -> False)

inductive CaptureSet.Chaining : Context n m k -> CaptureSet n k -> CaptureSet n k -> Prop where
| mk :
  CaptureSet.Root C1 Γ D1 ->
  CaptureSet.Root C2 Γ D2 ->
  D1.Chaining D2 ->
  CaptureSet.Chaining Γ C1 C2

end Capybara
