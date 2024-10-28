import Cappy.Syntax
import Capless.CaptureSet
import Cappy.Translation.TContext
namespace Cappy

/-!
# Encoding of Capture Sets

The `CaptureSet.Interp` derivation defines the encoding of capture sets from Cappy to Capless. It is a 5-place judgement:
1. The mapping from reach capabilities to capture variables
2. The type context in Cappy
3. The input capture set
4. The interpretation
5. The output capture set
!-/

inductive CaptureSet.Interp : TMap n m k -> Context n m -> CaptureSet n -> Capless.CaptureSet n k -> Capless.CaptureSet n k -> Prop where
| i_empty :
  CaptureSet.Interp ρ Γ {} D {}
| i_union :
  CaptureSet.Interp ρ Γ C1 D D1 ->
  CaptureSet.Interp ρ Γ C2 D D2 ->
  CaptureSet.Interp ρ Γ (C1 ∪ C2) D (D1 ∪ D2)
| i_singleton :
  Context.Bound Γ x (S^C) ->
  CaptureSet.Interp ρ Γ C {c=ρ.reach x} C' ->
  CaptureSet.Interp ρ Γ {x=x} D C'
| i_reach :
  CaptureSet.Interp ρ Γ {x*=x} D {c=ρ.reach x}
| i_cap :
  CaptureSet.Interp ρ Γ {cap} D D

notation:20 "⟦" C1 "⟧^" D " ↝c[" ρ " | " Γ "] " C2 => CaptureSet.Interp ρ Γ C1 D C2

end Cappy
