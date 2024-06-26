import Capless.Context
import Capless.CaptureSet
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
  Context.Bound Γ x (EType.type (CType.capt C S)) ->
  Subcapt Γ {x} C
| evar :
  Context.Bound Γ x (EType.ex (CType.capt (CaptureSet.cweaken C) S)) ->
  -- Context.CBound Γ c (CBinding.inst {x}) ->
  Subcapt Γ {x} C
| cinstl :
  Context.CBound Γ c (CBinding.inst C) ->
  Subcapt Γ C (CaptureSet.csingleton c)
| cinstr :
  Context.CBound Γ c (CBinding.inst C) ->
  Subcapt Γ (CaptureSet.csingleton c) C
| reachl :
  Context.Bound Γ x (EType.exp c T) ->
  Subcapt Γ (CaptureSet.csingleton c) (CaptureSet.rsingleton x)
| reachr :
  Context.Bound Γ x (EType.exp c T) ->
  Subcapt Γ (CaptureSet.rsingleton x) (CaptureSet.csingleton c)

end Capless
