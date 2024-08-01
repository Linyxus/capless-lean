import Capless.Reduction
namespace Capless

inductive Progress : State n m k -> Prop where
| mk :
  Reduce state state' ->
  Progress state

theorem progress
  (ht : TypedState state E) :
  Progress state := by
  cases ht
  case mk hs ht hc =>
    cases ht
    case var => sorry
    case pack => sorry
    case sub => sorry
    case abs => sorry
    case tabs => sorry
    case cabs => sorry
    case app => sorry
    case tapp => sorry
    case capp => sorry
    case box => sorry
    case unbox => sorry
    case letin => sorry
    case letex => sorry
    case bindt => sorry
    case bindc => sorry

end Capless
