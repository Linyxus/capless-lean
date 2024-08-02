import Capless.Reduction
namespace Capless

inductive Progress : State n m k -> Prop where
| step :
  Reduce state state' ->
  Progress state
| halt_value {t : Term n m k} :
  t.IsValue ->
  Progress ⟨σ, Cont.none, t⟩
| halt_var :
  Progress ⟨σ, Cont.none, Term.var x⟩

theorem progress
  (ht : TypedState state E) :
  Progress state := by
  cases ht
  case mk hs ht hc =>
    induction ht
    case var =>
      cases hc
      case none => apply Progress.halt_var
      case cons =>
        apply Progress.step
        apply Reduce.rename
    case pack =>
      cases hc
      case none => apply Progress.halt_value; constructor
      case conse =>
        apply Progress.step
        apply Reduce.lift_ex
    case sub hsub ih _ _ =>
      apply ih <;> try trivial
      sorry
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
