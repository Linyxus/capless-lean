import Capybara.StaticSemantics.CaptureRoot
namespace Capybara

/-!
Separation checking.
-/

inductive RootSeparation : Context n m k -> CaptureRoot k -> CaptureRoot k -> Prop where
| symm :
  RootSeparation Γ r1 r2 ->
  RootSeparation Γ r2 r1
| ro :
  RORoot Γ r1 ->
  RORoot Γ r2 ->
  RootSeparation Γ r1 r2
| rw :
  RootSeparation Γ ⟨ε,c1⟩ r2 ->
  RootSeparation Γ ⟨ro,c1⟩ r2
| sep :
  Context.LookupC Γ c (cparam (CKind.Sep ⟨s,D⟩)) ->
  ReachRoot Γ D r2 ->
  RootSeparation Γ ⟨ε,c⟩ r2
| fresh :
  Context.LookupC Γ c1 (cparam CKind.Fresh) ->
  Context.LookupC Γ c2 (cparam CKind.Fresh) ->
  (c1 ≠ c2) ->
  RootSeparation Γ ⟨μ1,c1⟩ ⟨μ2,c2⟩

def Separation (Γ : Context n m k) (C1 C2 : CaptureSet n k) : Prop :=
  ∀r1 r2, ReachRoot Γ C1 r1 -> ReachRoot Γ C2 r2 -> RootSeparation Γ r1 r2

end Capybara
