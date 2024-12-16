import Capybara.Syntax
namespace Capybara

/-!
Subcapturing relation.

There are three structural rules:
- `subset`: if `C1 ⊆ C2`, then `C1` subcaptures `C2`.
- `trans`: if `C1` subcaptures `C2` and `C2` subcaptures `C3`, then `C1` subcaptures `C3`.
- `union`: if `C1` subcaptures `C` and `C2` subcaptures `C`, then `C1 ∪ C2` subcaptures `C`.

Two rules for variables, one for default (mutable) captures and the other for read-only captures. Two similar rules for capture set aliases.
-/
inductive Subcapturing : Context n m k -> CaptureSet n k -> CaptureSet n k -> Prop where
| subset :
  (C1 ⊆ C2) ->
  Subcapturing Γ C1  C2
| trans :
  Subcapturing Γ C1 C2 ->
  Subcapturing Γ C2 C3 ->
  Subcapturing Γ C1 C3
| union :
  Subcapturing Γ C1 C ->
  Subcapturing Γ C2 C ->
  Subcapturing Γ (C1 ∪ C2) C
| ro :
  Subcapturing Γ (C.ro) C
| var :
  Context.Lookup Γ x (CType.capt C m S) ->
  Subcapturing Γ ({x:=x}) (C.qualified (Mode.M m))
| rovar :
  Context.Lookup Γ x (CType.capt C m S) ->
  Subcapturing Γ ({x@ro:=x}) (C.qualified ro)
| cvar_l :
  Context.LookupC Γ c (calias C) ->
  Subcapturing Γ ({c@m:=c}) (C.qualified m)
| cvar_r :
  Context.LookupC Γ c (calias C) ->
  Subcapturing Γ (C.qualified m) ({c@m:=c})

notation:50 Γ " ⊢c " C1 "<:" C2 => Subcapturing Γ C1 C2

end Capybara
