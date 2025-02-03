import Capybara.Syntax
import Capybara.StaticSemantics.CaptureRoot
import Capybara.StaticSemantics.Separation
namespace Capybara

inductive Kinding : Context n m k -> CaptureSet n k -> CKind n k -> Prop where
| fresh :
  ForallRoot Γ C (λ r => FreshRoot Γ r) ->
  Kinding Γ C CKind.Fresh
| sep_mut :
  Separation Γ C D ->
  ForallRoot Γ C (λ r => MutRoot Γ r) ->
  Kinding Γ C (CKind.Sep ⟨SepMode.Mut, D⟩)
| sep_imm :
  Separation Γ C D ->
  ForallRoot Γ C (λ r => RORoot Γ r) ->
  Kinding Γ C (CKind.Sep ⟨SepMode.Imm, D⟩)

end Capybara
