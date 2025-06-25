import Capless.Context
import Capless.CaptureSet

/-!

# Subcapturing

`Subcapt Γ C1 C2` defines the subcapturing judgement `Γ ⊢ C1 <: C2` in Fig. 2. Most rules correspond directly to the rules on the paper. The `Subcapt.cinstl` and `Subcapt.cinstr` rules are for capture set variables bound by `Term.bindc`--they are transparent in the subcapturing relation.
-/

namespace Capless

inductive Subcapt : Context n m k -> CaptureSet n k -> CaptureSet n k -> Prop where
| trans :
  Subcapt Γ C1 C2 ->
  Subcapt Γ C2 C3 ->
  Subcapt Γ C1 C3
| subset :
  C1 ⊆ C2 ->
  Subcapt Γ C1 C2
| union :
  Subcapt Γ C1 C3 ->
  Subcapt Γ C2 C3 ->
  Subcapt Γ (C1 ∪ C2) C3
| var :
  Context.Bound Γ x (CType.capt C S) ->
  Subcapt Γ {x=x} C
| cinstl :
  Context.CBound Γ c (CBinding.inst C) ->
  Subcapt Γ C {c=c}
| cinstr :
  Context.CBound Γ c (CBinding.inst C) ->
  Subcapt Γ {c=c} C
| cbound :
  Context.CBound Γ c (CBinding.bound (CBound.upper C)) ->
  Subcapt Γ {c=c} C

notation:50 Γ " ⊢ " C1 " <:c " C2 => Subcapt Γ C1 C2

end Capless
