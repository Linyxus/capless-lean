import Cappy.Syntax.Context
namespace Cappy

inductive Subcapt : Context n m -> CaptureSet n -> CaptureSet n -> Prop where
| sc_trans :
  Subcapt Γ C1 C2 ->
  Subcapt Γ C2 C3 ->
  Subcapt Γ C1 C3
| sc_var :
  Context.Bound Γ x (S^C) ->
  Subcapt Γ {x=x} C
| sc_elem {C1 C2 : CaptureSet n} :
  C1 ⊆ C2 ->
  Subcapt Γ C1 C2
| sc_set :
  Subcapt Γ C1 C ->
  Subcapt Γ C2 C ->
  Subcapt Γ (C1 ∪ C2) C


end Cappy
