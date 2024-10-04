import Capless.Context
import Capless.Type

namespace Capless

inductive SType.Dealias : Context n m k -> SType n m k -> SType n m k -> Prop where
| refl :
  Dealias Γ S S
| step :
  Context.TBound Γ X (TBinding.inst S) ->
  Dealias Γ S S' ->
  Dealias Γ (SType.tvar X) S'


end Capless
