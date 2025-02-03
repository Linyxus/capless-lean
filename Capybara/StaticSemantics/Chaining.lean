import Capybara.StaticSemantics.CaptureRoot
namespace Capybara

/-!
`Γ ⊢ C1 >> C2` means that the effects of `C1` and `C2` are chainable.

Specifically, anything that has been dropped from `C1` cannot be mentioned by `C2` any more.
-/

inductive RootChaining : Context n m k -> CaptureRoot k -> CaptureRoot k -> Prop
| c_rw :
  RootChaining Γ ⟨Mode.M m1, c1⟩ r2
| c_drop :
  (c1 ≠ c2) ->
  RootChaining Γ ⟨drop,c1⟩ ⟨m,c2⟩

def Chaining (Γ : Context n m k) (C1 C2 : CaptureSet n k) : Prop :=
  ForallRoot Γ C1 (λ r1 =>
    ForallRoot Γ C2 (λ r2 =>
      RootChaining Γ r1 r2))

inductive DroppedRootChaining : Context n m k -> CaptureRoot k -> CaptureRoot k -> Prop
| c_chain :
  (c1 ≠ c2) ->
  DroppedRootChaining Γ ⟨m1,c1⟩ ⟨m2,c2⟩

def DroppedChaining (Γ : Context n m k) (C1 C2 : CaptureSet n k) : Prop :=
  ForallRoot Γ C1 (λ r1 =>
    ForallRoot Γ C2 (λ r2 =>
      DroppedRootChaining Γ r1 r2))

notation:50 Γ " ⊢ " C1 " >> " C2 => CaptureSet.Chaining Γ C1 C2
notation:50 Γ " ⊢ " C1 " drop>> " C2 => CaptureSet.DroppedChaining Γ C1 C2

end Capybara
