import Capybara.Syntax
import Capybara.StaticSemantics.CaptureRoot
import Capybara.StaticSemantics.Separation
namespace Capybara

inductive Kinding : Context n m k -> CaptureSet n k -> CKind n k -> Prop where
| fresh :
  (∀c m, ReachRoot Γ C ⟨Mode.M m,c⟩ -> Context.LookupC Γ c (cparam CKind.Fresh)) ->
  Kinding Γ C CKind.Fresh
| sep_mut :
  Separation Γ C D ->
  Kinding Γ C (CKind.Sep ⟨SepMode.Mut, D⟩)
| sep_imm :
  Separation Γ C D ->
  (∀r, ReachRoot Γ C r -> RORoot Γ r) ->
  Kinding Γ C (CKind.Sep ⟨SepMode.Imm, D⟩)

end Capybara
