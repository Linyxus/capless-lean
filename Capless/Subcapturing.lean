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
  Context.Bound Γ x (CType.capt C S) ->
  Subcapt Γ {x} C
| cinstl :
  Context.CBound Γ c (CBinding.inst C) ->
  Subcapt Γ C (CaptureSet.csingleton c)
| cinstr :
  Context.CBound Γ c (CBinding.inst C) ->
  Subcapt Γ (CaptureSet.csingleton c) C

end Capless
