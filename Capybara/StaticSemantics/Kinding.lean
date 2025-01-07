import Capybara.Syntax
import Capybara.StaticSemantics.CaptureRoot
namespace Capybara

/-!
Kinding of capture roots.
- `empty` and `union` are structural rules
- `k_ro`: a readonly access is immutable
- `k_imm`: any access to an immutable capture set variable is immutable
- `k_mut`: any access can be counted as mutable
- `k_fresh`: access to a fresh capture set variable is fresh
-/
inductive CaptureRoot.Kinding : Context n m k -> CaptureRoot k -> Kind -> Prop where
| empty : CaptureRoot.Kinding Γ {} Kind.Imm
| union :
  CaptureRoot.Kinding Γ D1 K ->
  CaptureRoot.Kinding Γ D2 K ->
  CaptureRoot.Kinding Γ (D1 ∪ D2) K
| k_ro :
  CaptureRoot.Kinding Γ (CaptureRoot.singleton c ro) Kind.Imm
| k_imm :
  Context.LookupC Γ c (cparam Kind.Imm) ->
  CaptureRoot.Kinding Γ (CaptureRoot.singleton c m) Kind.Imm
| k_mut :
  CaptureRoot.Kinding Γ (CaptureRoot.singleton c m) Kind.Mut
| k_fresh :
  Context.LookupC Γ c (cparam Kind.Fresh) ->
  CaptureRoot.Kinding Γ (CaptureRoot.singleton c m) Kind.Fresh

end Capybara
