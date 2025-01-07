import Capybara.Syntax
namespace Capybara

/-!
A capture root is a set of qualified access to abstract capture variables.
-/
inductive CaptureRoot (k : Nat) where
| empty : CaptureRoot k
| union : CaptureRoot k -> CaptureRoot k -> CaptureRoot k
| singleton : Fin k -> Mode -> CaptureRoot k

/-!
Instances of `CaptureRoot`: empty, union.
-/

instance : EmptyCollection (CaptureRoot k) := ⟨CaptureRoot.empty⟩
instance : Union (CaptureRoot k) := ⟨CaptureRoot.union⟩

/-!
The capture root of a capture set under a context.

The relation `CaptureSet.Root C Γ D` defines how a capture set `C` maps to its root capture variables `D`
under the context `Γ`. The root captures represent the original abstract capture variables that are the
source of the captures in the set. This relation is defined inductively with the following cases:

* Empty: An empty capture set maps to an empty root set
* Union: The root of a union of capture sets is the union of their roots
* Singleton: A singleton capture of a variable maps to the root of its type's capture set
* Parameter: A singleton capture of a parameter maps directly to that parameter with its mode
* Alias: A singleton capture of an alias maps to the root of its aliased capture set
-/
inductive CaptureSet.Root : CaptureSet n k -> Context n m k -> CaptureRoot k -> Prop where
| empty : CaptureSet.Root {} Context.empty {}
| union :
  Root C1 Γ D1 ->
  Root C2 Γ D2 ->
  Root (C1 ∪ C2) Γ (D1 ∪ D2)
| singleton :
  Context.Lookup Γ x (CType.capt C m0 S0) ->
  CaptureSet.Root (C.qualified m) Γ D ->
  CaptureSet.Root ({x@m:=x}) Γ D
| csingleton_param :
  Context.LookupC Γ c (cparam k) ->
  CaptureSet.Root ({c@m:=c}) Γ (CaptureRoot.singleton c m)
| csingleton_alias :
  Context.LookupC Γ c (calias C) ->
  CaptureSet.Root (C.qualified m) Γ D ->
  CaptureSet.Root ({c@m:=c}) Γ D

/-!
Membership of an access in a capture root.
-/
inductive CaptureRoot.HasElem : CaptureRoot k -> Fin k -> Mode -> Prop where
| union_l :
  HasElem D1 c m ->
  HasElem (D1 ∪ D2) c m
| union_r :
  HasElem D2 c m ->
  HasElem (D1 ∪ D2) c m
| singleton :
  HasElem (CaptureRoot.singleton c m) c m

end Capybara
