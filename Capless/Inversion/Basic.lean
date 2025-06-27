import Capless.Context
import Capless.Type

/-! # Basic Inversion Definitions

This file defines the basic `SType.Dealias` relation used throughout the inversion lemmas.
The `Dealias` relation represents type alias resolution, allowing a type variable to be
replaced by its instantiated type through the context.
-/

namespace Capless

inductive SType.Dealias : Context n m k -> SType n m k -> SType n m k -> Prop where
| refl :
  Dealias Γ S S
| step :
  Context.TBound Γ X (TBinding.inst S) ->
  Dealias Γ S S' ->
  Dealias Γ (SType.tvar X) S'


end Capless
