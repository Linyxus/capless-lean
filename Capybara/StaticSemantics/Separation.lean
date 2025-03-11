import Capybara.StaticSemantics.CaptureRoot
namespace Capybara

/-!
Separation checking.
-/

inductive RootSeparation : Context n m k -> CaptureRoot k -> CaptureRoot k -> Prop where
| s_symm :
  RootSeparation Γ r1 r2 ->
  RootSeparation Γ r2 r1
| s_ro :
  RORoot Γ r1 ->
  RORoot Γ r2 ->
  RootSeparation Γ r1 r2
| s_rw :
  RootSeparation Γ ⟨ε,c1⟩ r2 ->
  RootSeparation Γ ⟨ro,c1⟩ r2
| s_sep :
  Context.LookupC Γ c (cparam (CKind.Sep ⟨s,D⟩)) ->
  ReachRoot Γ D r2 ->
  RootSeparation Γ ⟨ε,c⟩ r2
| s_fresh :
  Context.LookupC Γ c1 (cparam CKind.Fresh) ->
  Context.LookupC Γ c2 (cparam CKind.Fresh) ->
  (c1 ≠ c2) ->
  RootSeparation Γ ⟨μ1,c1⟩ ⟨μ2,c2⟩

def Separation (Γ : Context n m k) (C1 C2 : CaptureSet n k) : Prop :=
  ForallRoot Γ C1 (λ r1 =>
    ForallRoot Γ C2 (λ r2 =>
      RootSeparation Γ r1 r2))

end Capybara
