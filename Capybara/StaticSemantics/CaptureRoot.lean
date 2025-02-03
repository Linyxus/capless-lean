import Capybara.Syntax
namespace Capybara

/-!
A capture root is described by an abstract capture parameter and an access mode. A capture root `m c` being reachable from a capture set `C` means that `C` could access `c` at mode `m`.
-/
structure CaptureRoot (k : Nat) : Type where
  m : Mode
  c : Fin k

def CaptureRoot.rename (r : CaptureRoot k) (f : FinFun k k') : CaptureRoot k' :=
  match r with
  | ⟨m,c⟩ => ⟨m,f c⟩

/-!
`ReachRoot Γ C m c` means that the root `c` is reachable at access mode `m` from the capture set `C` under the context `Γ`.
-/
inductive ReachRoot : Context n m k -> CaptureSet n k -> CaptureRoot k -> Prop where
| union_l :
  ReachRoot Γ C1 ⟨m,c⟩ ->
  ReachRoot Γ (C1 ∪ C2) ⟨m,c⟩
| union_r :
  ReachRoot Γ C2 ⟨m,c⟩ ->
  ReachRoot Γ (C1 ∪ C2) ⟨m,c⟩
| var :
  Context.Lookup Γ x (S^[m]C) ->
  ReachRoot Γ ((C.qualified (Mode.M m)).qualified mu) ⟨mu',c⟩ ->
  ReachRoot Γ ({x@mu:=x}) ⟨mu',c⟩
| cvar_alias :
  Context.LookupC Γ c (calias C) ->
  ReachRoot Γ (C.qualified mu) ⟨mu',c'⟩ ->
  ReachRoot Γ ({c@mu:=c}) ⟨mu',c'⟩
| cvar :
  Context.LookupC Γ c (cparam K) ->
  ReachRoot Γ ({c@mu:=c}) ⟨mu,c⟩

def RootPred (k : Nat) := CaptureRoot k -> Prop

inductive ForallRoot : Context n m k -> CaptureSet n k -> RootPred k -> Prop where
| r_union :
  ForallRoot Γ C1 P ->
  ForallRoot Γ C2 P ->
  ForallRoot Γ (C1 ∪ C2) P
| r_var :
  Context.Lookup Γ x (S^[m]C) ->
  ForallRoot Γ ((C.qualified (Mode.M m)).qualified mu) P ->
  ForallRoot Γ ({x@mu:=x}) P
| r_cvar_alias :
  Context.LookupC Γ c (calias C) ->
  ForallRoot Γ (C.qualified mu) P ->
  ForallRoot Γ ({c@mu:=c}) P
| r_cvar :
  Context.LookupC Γ c (cparam K) ->
  (P ⟨mu,c⟩) ->
  ForallRoot Γ ({c@mu:=c}) P

/-!
The following judgements are predicates on the *kinds* of a capture root.
A capture root can be:
- read-only (`RORoot`), signifying a readonly access;
- mutable (`MutRoot`), signifying a read-write access;
- fresh (`FreshRoot`), signifying a read-write access to root that is known to be fresh.
-/
inductive RORoot : Context n m k -> CaptureRoot k -> Prop where
| r_ro :
  RORoot Γ ⟨ro,c⟩
| r_imm :
  Context.LookupC Γ c (cparam (CKind.Sep ⟨SepMode.Imm, D⟩)) ->
  RORoot Γ ⟨Mode.M m,c⟩
inductive MutRoot : Context n m k -> CaptureRoot k -> Prop where
| r_mut :
  MutRoot Γ ⟨Mode.M m,c⟩
inductive FreshRoot : Context n m k -> CaptureRoot k -> Prop where
| r_fresh :
  Context.LookupC Γ c (cparam CKind.Fresh) ->
  FreshRoot Γ ⟨Mode.M m,c⟩

end Capybara
