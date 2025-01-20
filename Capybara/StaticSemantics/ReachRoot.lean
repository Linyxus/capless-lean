import Capybara.Syntax
namespace Capybara

/-!
`ReachRoot Γ C m c` means that the root `c` is reachable at access mode `m` from the capture set `C` under the context `Γ`.
-/
inductive ReachRoot : Context n m k -> CaptureSet n k -> Mode -> Fin k -> Prop where
| union_l :
  ReachRoot Γ C1 m c ->
  ReachRoot Γ (C1 ∪ C2) m c
| union_r :
  ReachRoot Γ C2 m c ->
  ReachRoot Γ (C1 ∪ C2) m c
| var :
  Context.Lookup Γ x (S^[m]C) ->
  ReachRoot Γ ((C.qualified (Mode.M m)).qualified mu) mu' c ->
  ReachRoot Γ ({x@mu:=x}) mu' c
| cvar_alias :
  Context.LookupC Γ c (calias C) ->
  ReachRoot Γ (C.qualified mu) mu' c' ->
  ReachRoot Γ ({c@mu:=c}) mu' c'
| cvar :
  ReachRoot Γ ({c@mu:=c}) mu c

end Capybara
