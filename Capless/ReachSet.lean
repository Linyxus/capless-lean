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
  ReachSet Γ {c=c|L} (.singleton (.creach c) (K.intersect L))
| label :
  Context.LBound Γ x c S ->
  ReachSet Γ {x=x|L} {x=x|(Kind.classifier c).intersect L}
| var_reach :
  ReachSet Γ {x=x|K} R ->
  ReachSet Γ {x^=x|K} R
| cvar_creach :
  ReachSet Γ {c=c|K} R ->
  ReachSet Γ {c^=c|K} R
| absurd : K.IsEmpty -> ReachSet Γ (.singleton s K) {}

theorem ReachSet.apply_proj (hr : ReachSet Γ C R) : ReachSet Γ (C.proj K) (R.proj K) := by
  induction hr
  case empty => apply empty
  case union ha hb => apply! union
  case var ih =>
    rw [CaptureSet.proj_proj] at ih
    apply! var
  case cinstr ih =>
    rw [CaptureSet.proj_proj] at ih
    apply! cinstr
  case cbound ih =>
    rw [CaptureSet.proj_proj] at ih
    apply! cbound
  case ckind hb =>
    simp only [CaptureSet.proj]
    rw [Kind.intersect.assoc]
    apply ckind hb
  case label hb =>
    simp only [CaptureSet.proj]
    rw [Kind.intersect.assoc]
    apply label hb
  case var_reach ih =>
    simp only [CaptureSet.proj]
    apply var_reach ih
  case cvar_creach ih =>
    simp only [CaptureSet.proj]
    apply cvar_creach ih
  case absurd =>
    apply absurd
    apply! Kind.intersect.is_empty_l

end Capless
