import Capless.Store
import Capless.Type
import Capless.Reduction
namespace Capless

inductive Preserve : EType n m k -> State n' m' k' -> Prop where
| mk :
  TypedState state E ->
  Preserve E state
| mk_weaken :
  TypedState state E.weaken ->
  Preserve E state
| mk_tweaken :
  TypedState state E.tweaken ->
  Preserve E state
| mk_cweaken :
  TypedState state E.cweaken ->
  Preserve E state

theorem preservation
  (hr : Reduce state state')
  (ht : TypedState state E) :
  Preserve E state' := by
  cases hr
  case apply hl => sorry
  case tapply  hl=> sorry
  case capply hl => sorry
  case unbox hl => sorry
  case push => sorry
  case push_ex => sorry
  case rename => sorry
  case rename_ex => sorry
  case lift hv => sorry
  case tlift => sorry
  case clift => sorry


end Capless
