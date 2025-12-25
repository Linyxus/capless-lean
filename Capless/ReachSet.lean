import Capless.CaptureSet
import Capless.Context

namespace Capless

/-- Computes the reach set of a capture set. The reach set should only consist of capture variables and -/
inductive ReachSet : Context n m k -> CaptureSet n k -> CaptureSet n k -> Prop where
| empty : ReachSet Γ .empty .empty
| union :
  ReachSet Γ C1 R1 ->
  ReachSet Γ C2 R2 ->
  ReachSet Γ (C1 ∪ C2) (R1 ∪ R2)
| var :
  Context.Bound Γ x (S^C) ->
  ReachSet Γ (C.proj L) R ->
  ReachSet Γ {x=x|L} R
| cinstr :
  Context.CBound Γ c (CBinding.inst C) ->
  ReachSet Γ (C.proj L) R ->
  ReachSet Γ {c=c|L} R
| cbound :
  Context.CBound Γ c (CBinding.bound (CBound.upper C)) ->
  ReachSet Γ (C.proj L) R ->
  ReachSet Γ {c=c|L} R
| ckind :
  Context.CBound Γ c (CBinding.bound (CBound.kind K)) ->
  ReachSet Γ {c=c|L} {c=c|K.intersect L}
| label :
  Context.LBound Γ x c S ->
  ReachSet Γ {x=x|L} {x=x|(Kind.classifier c).intersect L}
| absurd : K.IsEmpty -> ReachSet Γ (.singleton s K) {}

end Capless
